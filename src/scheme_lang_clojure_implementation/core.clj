(ns scheme-lang-clojure-implementation.core
  (:import (java.util HashMap)))
(defonce apply-in-underlying apply)
(declare eval- apply eval-assignment eval-definition eval-if eval-sequence make-procedure lookup-variable-value list-of-values)

; Syntax of the language. Expression predicates
(defn self-evaluating?
  [exp]
  (cond (number? exp) true
        (string? exp) true
        :else false
        ))

(defn variable?
  [exp]
  (or (symbol? exp) (boolean? exp))) ;boolean is added because clojure reader doesn't read true and false as symbols,but as booleans

(defn tagged-list?
  [exp tag]
  (if (seq? exp)
    (= (first exp) tag)
    false
    ))

(defn quoted? [exp]  (tagged-list? exp 'quote))
(defn text-of-quotation [exp _] (second exp))

(defn assignment-variable [exp] (second exp))
(defn assignment-value [exp] (nth exp 2))

(defn definition-variable [exp]
  (if (symbol? (second exp))
    (second exp)
    (first (second exp))))

(defn make-lambda [parameters body]
  (cons 'lambda (cons parameters body)))

(defn definition-value [exp]
  (if (symbol? (second exp))
    (nth exp 2)
    (make-lambda (rest (second exp)) ; formal parameters
                 (rest (rest exp))))); body

(defn lambda-parameters [exp] (second exp))
(defn lambda-body [exp] (rest (rest exp)))

(defn if-predicate [exp] (second exp))
(defn if-consequent [exp] (nth exp 2))
(defn if-alternative [exp]
  (let [alternative (nth exp 3)]
    (if (not (nil? alternative))
      alternative
      'false)))

(defn make-if
  [predicate consequent alternative]
  (list 'if predicate consequent alternative))

(defn begin-actions [exp] (rest exp))
(defn last-exp? [seq] (empty? (rest seq)))
(defn first-exp [seq] (first seq))
(defn rest-exps [seq] (rest seq))

(defn make-begin [seq] (cons 'begin seq))
(defn sequence->exp [seq]
  (cond (empty? seq) seq
        (last-exp? seq) (first-exp seq)
        :else (make-begin seq)))

;Exercise 4.2
;a) Since application? predicate tests only if `exp` is sequence (pair? in book), it must be last in eval cond,
;   after all special forms, otherwise we would evaluate special forms as procedure applications.
;   solution may be to change application? pred so that it checks if first element is not some special form keyword (like define, if,cond, etc...)
;b) We should change application? procedure to this: (defn application? [exp] (tagged-list? exp 'call)) and change operator and operands selector so they select next element.

(defn application? [exp] (seq? exp))
(defn operator [exp] (first exp))
(defn operands [exp] (rest exp))
(defn no-operands? [ops] (or (nil? ops) (zero? (count ops))))
(defn first-operand [ops] (first ops))
(defn rest-operands [ops] (rest ops))

(defn cond? [exp] (tagged-list? exp 'cond))
(defn cond-clauses [exp] (rest exp))
(defn cond-predicate [clause] (first clause))
(defn cond-else-clause? [clause]
        (= (cond-predicate clause) 'else))
(defn cond-actions
  [clause]
  (let [actions (rest clause)]
    (if (= '=> (first actions))
        (list (list (second actions) (cond-predicate clause)))
      actions)))

(defn expand-clauses [clauses]
  (if (empty? clauses)
    'false
    (let [f (first clauses)
          r (rest clauses)]
      (if (cond-else-clause? f)
        (if (empty? r)
          (sequence->exp (cond-actions f))
          (throw (ex-info "Else clause isn't last" {:clauses clauses :procedure :cond->if})))
        (make-if (cond-predicate f)
                 (sequence->exp (cond-actions f))
                 (expand-clauses r))))))

(defn cond->if [exp] (expand-clauses (cond-clauses exp)))

(defn list-of-values
  [exps env]
  (if (no-operands? exps)
    (list)
    (let [first-operand-eval (eval- (first-operand exps) env)
          rest-operands-eval (list-of-values (rest-operands exps) env)
          ]
      (cons first-operand-eval rest-operands-eval)))) ;Exercies 4.1

(defn eval-if
  [exp env]
  (if (eval- (if-predicate exp) env)
      (eval- (if-consequent exp) env)
      (eval- (if-alternative exp) env)))

(defn eval-sequence
  [exps env]
  (cond
    (last-exp? exps) (eval- (first-exp exps) env)
    :else (do  (eval- (first-exp exps) env)
               (eval-sequence (rest-exps exps) env))))

(defn enclosing-environment [env] (rest env))
(defn first-frame [env] (first env))
(defonce the-empty-environment '())
(defn make-frame
  [variables values]
  (let [frame (HashMap.)]
    (loop [vars variables vals values]
      (when (not-empty vars)
        (do
          (.put frame (first vars) (first vals))
          (recur (rest vars) (rest vals)))))
    frame))

(defn frame-variables [frame] (.values frame))
(defn frame-values [frame] (.keySet frame))

(defn add-binding-to-frame!
  [var val frame]
  (.put frame var val))

(defn extend-environment
  [vars vals base-env]
  (if (= (count vars) (count vals))
    (cons (make-frame vars vals) base-env)
    (if (< (count vars) (count vals))
      (throw (ex-info "Too many arguments supplied" {:vars vars :vals vals}))
      (throw (ex-info "Too few arguments supplied" {:vars vars :vals vals})))))

(defn lookup-variable-value
  [var env]
  (loop [e env]
    (when (= e the-empty-environment)
      (throw (ex-info "Unbound variable" {:variable var :procedure :lookup-variable-value})))
    (let [frame (first-frame e)]
      (if (.containsKey frame var)
        (.get frame var)
        (recur (enclosing-environment e))))))

(defn set-variable-value!
  [var val env]
  (loop [e env]
    (when (= e the-empty-environment)
      (throw (ex-info "Unbound variable" {:variable var :procedure :lookup-variable-value})))
    (let [frame (first-frame env)]
      (if (.containsKey frame var)
        (add-binding-to-frame! var val frame)
        (recur (enclosing-environment e))))))

(defn eval-assignment
  [exp env]
  (set-variable-value! (assignment-variable exp)
                       (eval- (assignment-value exp) env)
                       env)
  'ok);We have chosen here to return the symbol ok as the value of an assignment or a definition

(defn define-variable!
  [var val env]
  (let [frame (first-frame env)]
    (add-binding-to-frame! var val frame)))
(defn eval-definition
  [exp env]
  (define-variable! (definition-variable exp)
                    (eval- (definition-value exp) env)
                    env)
  'ok)
(defn eval-and
  [exp env] (let [expressions (rest exp)] ;Exercise 4.4
              (if (empty? expressions)
                'true
                (loop [exps expressions]
                  (let [first-evaluated (eval- (first exps) env)]
                    (cond (empty? (rest exps)) first-evaluated
                          (not first-evaluated) 'false
                          :else (recur (rest exps))))))))

(defn eval-or
  [exp env]
  (let [expressions (rest exp)] ;Exercise 4.4
                  (if (empty? expressions)
                    'false
                    (loop [exps expressions]
                      (let [first-evaluated (eval- (first exps) env)]
                        (cond first-evaluated first-evaluated
                              (empty? (rest exps)) 'false
                              :else (recur (rest exps))
                              ))))))

(defn named-let? [exp]
  (= (count exp) 4))

(defn let-body [exp] (rest (rest exp)))

(defn let-vars
  [exp]
  (let [declarations (second exp)]
    (map first declarations)))

(defn make-let
  [bindings body]
  (cons 'let (cons bindings body)))

(defn let-exps
  [exp]
  (let [declarations (second exp)]
    (map second declarations)))

(defn let->combination
  [exp]
  (if (named-let? exp)
    ();TODO
    (cons (make-lambda (let-vars exp) (let-body exp))
          (let-exps exp))))

;Exercise 4.3
(defonce operation-table {'quote text-of-quotation
                          'set! eval-assignment
                          'define eval-definition
                          'if eval-if
                          'lambda (fn [exp env ] (make-procedure (lambda-parameters exp) (lambda-body exp ) env))
                          'begin (fn [exp env] (eval-sequence (begin-actions exp) env))
                          'cond (fn [exp env] (eval- (cond->if exp) env))
                          'and eval-and
                          'or eval-or
                          'let (fn [exp env] (eval- (let->combination exp) env))})

(defn eval-
  [exp env]
  (cond (self-evaluating? exp) exp
        (variable? exp) (lookup-variable-value exp env)
        ;(quoted? exp) (text-of-quotation exp)
        ;(assignment? exp) (eval-assignment exp env)
        ;(definition? exp) (eval-definition exp env)
        ;(if? exp) (eval-if exp env)
        ;(lambda? exp) (make-procedure (lambda-parameters exp)
        ;                              (lambda-body exp)
        ;                              env)
        ;(begin? exp)  (eval-sequence (begin-actions exp) env)
        ;(cond? exp) (eval- (cond->if exp) env)
        (get operation-table (first exp)) ((get operation-table (first exp)) exp env)
        (application? exp) (apply (eval- (operator exp) env)
                                  (list-of-values (operands exp) env))
        :else
        (throw (ex-info "Unknown expression type" {:expression exp :fn :EVAL})))
  )


(defn make-procedure [parameters body env]
  (list 'procedure parameters body env)
  )
(defn compound-procedure? [p]
  (tagged-list? p 'procedure))

(defn procedure-parameters [p] (second p))
(defn procedure-body [p]  (nth p 2))
(defn procedure-environment [p] (nth p 3))

(defonce primitive-procedures
        [['car first]
         ['cdr rest]
         ['cons cons]
         ['null? nil?]
         ['true? true?]
         ['false? false?]
         ['inc inc]
         ['+ +]
         ['- -]
         ['/ /]
         ['equal? =]])

(def primitive-procedure-names (map first primitive-procedures))
(def primitive-procedure-objects (map (fn [proc] (list 'primitive (second proc))) primitive-procedures))

(defn setup-environment []
        (let [initial-env
                (extend-environment primitive-procedure-names
                                    primitive-procedure-objects
                                    the-empty-environment)]
          (define-variable! 'true true initial-env)
          (define-variable! 'false false initial-env)
          initial-env))

(defn primitive-procedure? [proc]
        (tagged-list? proc 'primitive))

(defn primitive-implementation [proc] (second proc))

(defn apply-primitive-procedure
  [proc args]
        (apply-in-underlying
          (primitive-implementation proc) args))

(defn apply
  [procedure arguments]
        (cond (primitive-procedure? procedure) (apply-primitive-procedure procedure arguments)

              (compound-procedure? procedure) (do
                                                (eval-sequence
                                                  (procedure-body procedure)
                                                  (extend-environment
                                                    (procedure-parameters procedure)
                                                    arguments
                                                    (procedure-environment procedure)))
                                                )
              :else
              (throw (ex-info "Unknown procedure type" {
                                                        :procedure procedure
                                                        :arguments arguments}))))

;REPL
(def input-prompt ";;; M-Eval input:")
(def output-prompt ";;; M-Eval value:")

(defn prompt-for-input [s]
  (newline) (println s))
(defn announce-output [s]
        (newline) (println s))

(defn user-print [object]
        (if (compound-procedure? object)
          (println (list 'compound-procedure
                         (procedure-parameters object)
                         (procedure-body object)
                         '<procedure-env>))
          (println object)))

(defonce the-global-environment (setup-environment))
(defn driver-loop []
        (prompt-for-input input-prompt)
        (let [input (read-string (read-line))
              output (eval- input the-global-environment)]
            (announce-output output-prompt)
            (user-print output))
        (driver-loop))

(defn -main
  []
  (driver-loop))

;(define (fib n) (let fib-iter ((a 1) (b 0) (count n)) (if (= count 0) b (fib-iter (+ a b) a (- count 1)))))