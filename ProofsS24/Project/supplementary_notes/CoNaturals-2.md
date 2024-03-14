# CoNatural Numbers

## Embedding Natural Numbers into Co-Natural Numbers

Recall that we defined the type of **co-natural numbers**, denoted by $\mathbb{N}_\infty$, to be the type of decreasing binary sequences.

We want to embed the natural numbers into the co-natural numbers. Recall that from the last worksheet we associated to every natural number $n$ a binary sequence $d(n) : \mathbb{N} \to 2$ consisting of $n$ copies of $1$ followed by $0$s. More precisely, $d(n)$ is defined by $d(n)(m) = 1$ if $m < n$ and $d(n)(m) = 0$ if $m \geq n$. 

> * Warning: There was a typo in the last worksheet, where we wrote $m \leq n$ instead of $m < n$.*

In Lean code

```lean
def binSeqOf (n : ℕ) : BinSeq := 
fun i => if i < n then one else zero
```

**Exercise**
Give a full proof that the sequence $d(n)$ is a co-natural number for every natural number $n$. 

We say that a function is __injective__ (aka __one-to-one__) if it maps distinct elements to distinct elements. Equivalently, a function $f : A \to B$ is injective if for all $x, y \in A$, if $f(x) = f(y)$, then $x = y$. In Lean, 

```lean 
def Injective (f : A → B) := ∀ x y, f x = f y → x = y
```

**Exercise**
Give a full proof that the function $n \mapsto d(n)$ is injective.

We say that a function is __surjective__ (aka __onto__) if every element in the codomain is the image of some element in the domain. Equivalently, a function $f : A \to B$ is surjective if for all $y \in B$, there exists $x \in A$ such that $f(x) = y$. In Lean, 

```lean
def Surjective (f : A → B) := ∀ y, ∃ x, f x = y
```

**Exercise**
Is the function $n \mapsto d(n)$ surjective?



## Making Co-Natural Numbers Out Of Binary Sequences

By definition, every co-natural numbers is a decreasing binary sequence, and this gives rise to a function $\iota : \mathbb{N}_\infty \to (2 \to \mathbb{N})$ by forgetting that the sequence is decreasing.

Not every binary sequence is a co-natural number. However, we can force a binary sequence to be a co-natural number by taking its decreasing part.

In Lean, we can define this in a recursive way as follows:

```lean
def Decreasing.mk (a : ℕ → 𝟚) : ℕ → 𝟚
  | 0 => a 0
  | n + 1 => min (a (n + 1)) (mk a n)
```  

**Exercise**
1. Describe what the function `Decreasing.mk` does. What is the output of `Decreasing.mk` for the input $i(n)$? What is the output of `Decreasing.mk` for the input $d(n)$? What is the output of `Decreasing.mk` for the alternating sequence $0, 1, 0, 1, 0, 1, \ldots$?
2. Prove that the output of `Decreasing.mk` is a decreasing binary sequence, and therefore a co-natural number.

We say that a function is idempotent if applying it twice is the same as applying it once. For instance the floor and ceiling functions are idempotent, i.e. $\lfloor \lfloor x \rfloor \rfloor = \lfloor x \rfloor$, and $\lceil \lceil x \rceil \rceil = \lceil x \rceil$.

**Exercise**
Show that the function `Decreasing.mk` is idempotent, i.e. `Decreasing.mk (Decreasing.mk a) = Decreasing.mk a`.

**Exercise**
Show that the function `Decreasing.mk` is not injective.

We already constructed a function $d : \mathbb{N} \to \mathbb{N}_\infty$. We can now construct a function $\rho :  (2 \to \mathbb{N}) \to \mathbb{N}_\infty$ which takes a binary sequence and returns the decreasing part of the sequence.

**Exercise**
Show that the function $\rho$ is a left inverse of the function $\iota$, i.e. $\rho \circ \iota = \text{id}_{\mathbb{N}_\infty}$.

**Exercise**
Use this to prove that the function $\rho$ is surjective.
