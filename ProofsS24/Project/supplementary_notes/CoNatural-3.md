# CoNatural Numbers

## Lexicographical Order 

The lexicographic or dictionary order is a generalization of the alphabetical order of words in a dictionary. It is a way of ordering a set of words based on the alphabetical order of their component letters. 

For instance the words "apple", "banana", "cherry" and "date" are ordered lexicographically as follows:

`
apple < banana < cherry < coconut
`

For instance `apple < banana` because the first letter of `apple` is `a` and the first letter of `banana` is `b`. Since `a < b`, we have `apple < banana`.

The type `List ℕ` admits a lexicographical order. For instance, the lists `[1,2,3]` and `[1,2,4]` are ordered lexicographically as follows:

`
[1,2,3] < [1,2,4]
`

How about lists of different lengths? For instance, how do we compare `[1,2,2]` and `[1,2,2,4]`? Since the first three elements of both lists are the same, we pick the longer list as the greater one. Thus `[1,2,2] < [1,2,2,4]`.

In Lean the lexicographical order on `List ℕ` can be defined as follows:

```lean
inductive List.Lex : List ℕ → List ℕ → Prop
  | nil {a l} : Lex [] (a :: l)
  | cons {a l₁ l₂} (h : Lex l₁ l₂) : Lex (a :: l₁) (a :: l₂)
  | rel {a l b l'} (h : Nat.le a b) : Lex (a :: l) (b :: l')
```

We say that an order relation is Trichotomous if for any two elements $a$ and $b$ one and only one of the following holds: $a < b$, $a = b$ or $a > b$. 


**Exercise**
Write a full mathematical argument why the lexicographical order on `List ℕ` is trichotomous.



## Lexicographical Order On Binary Sequences

**Exercise**
Define the lexicographical order on the cartesian product $\mathbb{N} \times \mathbb{N}$. How is this order different than the standard pointwise order on $\mathbb{N} \times \mathbb{N}$? Give examples. 


**Exercise**
Define the lexicographical order on binary sequences. 



