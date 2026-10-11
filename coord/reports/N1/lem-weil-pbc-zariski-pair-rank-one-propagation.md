## Worker report

The module `Sheaf.RingTheory.ZariskiPairRankOnePropagation` states
`RingHom.zariskiPair_rank_one_propagation` for commutative rings `A`, `B` with an
`A`-algebra structure. The `[Module.Finite A B]` and
`[Module.FinitePresentation A B]` binders render finite generation and finite
presentation. The ideal `I : Ideal A` and `hI : I ≤ Ideal.jacobson (⊥ : Ideal A)`
render containment in the Jacobson radical. `hflat` is
`RingHom.Flat (algebraMap A B)`, the recorded flat ring-map notion. `hquot` is
bijectivity of the induced quotient map
`Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map`,
which renders the isomorphism `A/I ≅ B/IB`. The conclusion quantifies every
prime ideal `p` (with `[p.IsPrime]`) and gives a linear equivalence from the
localized module `LocalizedModule p.primeCompl B` to
`Localization.AtPrime p`, exactly a free module of rank one over `A_p`.

Dependencies used are Mathlib declarations `Module.Finite` (the node
`def-weil-finitely-generated-module`), `RingHom.Flat` (the node
`def-weil-pbc-flat-ring-map`), and `Localization.AtPrime` together with
`LocalizedModule` (the node `def-weil-pbc-localization-at-prime`). Their
recorded declarations are used directly; no dependency module was needed.

Edge cases checked include the zero ring and zero ideal (the Jacobson inclusion
and quotient-map hypothesis remain literal), arbitrary universe levels `u,v`,
and every prime including the empty spectrum case. No field or nonzero-rank
hypothesis is added.

Searches for an existing combined statement: `msearch.py leanfinder` and
`loogle` for finite flat quotient rank-one propagation returned only local
constancy/rank-at-stalk ingredients; grep of Mathlib `FreeLocus`, `Flat`, and
`Jacobson` found no quotient/Jacobson propagation theorem. `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this statement.

## Earlier second reading (a previous round; superseded)

The theorem signature was reread against the node. `A` and `B` are commutative
rings; finite generation, finite presentation, flatness, Jacobson containment,
and quotient isomorphism are each represented by the corresponding binder or
hypothesis. The conclusion quantifies all prime ideals and states that the
localization of `B` is linearly equivalent to the localized base ring, which is
precisely free rank one. No clause or edge case from the node was omitted.

## Second reading by N1

I read the node statement, its source place (Stacks, More on Algebra, Tag 0ELZ),
and the dependency records before checking the module. The objects and hypotheses
match item by item:

- `A : Type u`, `B : Type v`, `[CommRing A]`, `[CommRing B]`, and
  `[Algebra A B]` render the two commutative rings and the ring homomorphism.
- `I : Ideal A` and `hI : I ≤ Ideal.jacobson (⊥ : Ideal A)` render the ideal and
  its containment in the intersection of maximal ideals.
- `[Module.Finite A B]` and `[Module.FinitePresentation A B]` render finite
  generation and finite presentation of `B` as an `A`-module.
- `hflat : RingHom.Flat (algebraMap A B)` renders flatness of the ring map.
- `hquot` is bijectivity of `Ideal.quotientMap (I.map (algebraMap A B))
  (algebraMap A B) Ideal.le_comap_map`, exactly the induced map
  `A/I → B/IB` required to be an isomorphism.
- The conclusion quantifies every prime `p : Ideal A` with `[p.IsPrime]` and
  gives `Nonempty (LocalizedModule p.primeCompl B ≃ₗ[Localization.AtPrime p]
  Localization.AtPrime p)`, which is precisely that `B_p` is free of rank one over
  `A_p`.

No extra Noetherian, field, nonzero, characteristic, or rank assumptions occur;
`u` and `v` are independent and the empty spectrum and zero ring remain covered.
The zero ideal is allowed, and the Jacobson and quotient conditions are literal.
The localized-module and `Localization.AtPrime` declarations are the recorded
Mathlib leaves of `def-weil-pbc-localization-at-prime`; `Module.Finite` and
`RingHom.Flat` likewise use their recorded declarations directly. The source
proof's three steps (finite projective/local constant rank, rank one on `V(I)`,
and the Jacobson maximal-ideal argument) are recorded in the theorem docstring.

I independently searched with `msearch.py` (LeanFinder and Loogle queries for
finite flat quotient/Jacobson rank propagation), `rg` over Mathlib,
`WeilConjectures/`, and `lean/Sheaf/`; all found only component lemmas and no
existing combined declaration. No mismatch was found, so no code or statement
change was needed. The module compiles cleanly with only its intentional `sorry`.
