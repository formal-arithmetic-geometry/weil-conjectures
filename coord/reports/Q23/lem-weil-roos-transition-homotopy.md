## Worker report

The delivery states `CategoryTheory.RoosTransition.roos_transition_homotopy` in
`Sheaf.CategoryTheory.RoosTransitionHomotopy`. Its only theorem has proof `sorry`.
The actual product transition and finite telescoping sum have real definitions;
there is no chosen arbitrary comparison, hollow object, or postponed definition.
The helper predicate `TransitionHomotopy` writes the coordinate assertions once
so the constant-coefficient and algebra-coefficient clauses have exactly the same
meaning. All six declarations belong to this node and are in `lean.declarations`.
No new node or dependency repair is needed. The mathematical statement is unchanged.
The two added statement dependencies are already landed definition nodes used to
avoid duplicating the Roos construction and arithmetic product maps.

Sources read: `literature/stacks-project/sites-cohomology.tex`, lines 5035-5125,
Tag 0941, `lemma-derived-limit-is-ok`; `literature/stacks-project/algebra.tex`,
lines 17465-17525, Tag 00LR, `lemma-homotopic-equal-homology`; and all ten steps of
this node's explicitly agent-formulated proof. Tag 0941 supplies the Roos context,
not the forward subsequence homotopy. The source attribution preserves that
qualification. The module docstring and theorem docstring give this attribution,
and the latter reproduces the ten-step proof plan.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Small site C | `C : Type uC`, `Category.{vC} C`, `J : GrothendieckTopology C`; the coefficient/module universe is `max uC vC r`, containing both site universes without equating them. |
| Commutative ring A | `A : Type (max uC vC r)` and `[CommRing A]`. |
| Constant ring sheaf | `(constantSheaf J RingCat).obj (RingCat.of A)`, using the recorded sheafification of the constant presheaf. Forgetting commutativity when entering RingCat does not change its data. |
| Abelian category of module sheaves | `ringedSiteModules` from the dependency, transparently `SheafOfModules`. `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` supply Mathlib's canonical Abelian instance; `HasSheafify J RingCat` supplies the constant sheaf. These are the standard size/sheafification interfaces on a small site, not extra mathematical restrictions. |
| Countable products exact in A-modules | `HasExactLimitsOfShape (Discrete ℕ)` for that module category. Countable product existence is inferred from the standard sheaf-of-modules limits. Discrete natural-number products express the countable-product hypothesis; every countable family embeds into this case. |
| Strict tower of cochain complexes | `X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ` inside `TransitionHomotopy`; `X.asFunctor` is the evaluated tower of complexes. Strict tower maps are `a : X ⟶ Y`. This is the recorded inverse-system functor interface, not an inverse system in the derived category. |
| Positive levels n ≥ 1 | Lean level `n` denotes paper level `n+1`. No initial positive level is omitted. |
| Integer e ≥ 1 | `(e : ℕ) (he : 0 < e)`, exactly the positive integers. Negative/zero integers are not in the node's domain. |
| Subsequence K_en with composite transitions | Existing `StrictTowerArithmetic.complexRestriction D e`; its index is `e*(n+1)-1`. Its morphisms are the original functor's composites, so T_(n,n)=1 and the composition law follow from the tower functor. |
| U, shift s, f=1-s | Existing `roosP X` and `roosU X`; the latter is the recorded `towerTransitionEndomorphism`, with coordinate π_n−π_(n+1)t_n. |
| R(K)=Cone(f)[−1], displayed differential | Existing `roosF.obj X` and `roosχ X p`; these are exactly the shifted cone and the target-first coordinate order `(y,x)` from `def-weil-strict-roos-model`, with d(y,x)=(-dy-fx,dx). No replacement complex or arbitrary coordinate isomorphism is introduced. |
| a_e(x)_n=x_en | Existing `StrictTowerArithmetic.selection e X.asFunctor`. |
| b_e(y)_n=Σ_(en ≤ i < e(n+1)) T_(en,i)y_i | Existing `StrictTowerArithmetic.block e X.asFunctor`: a sum over `Finset.range e` with original predecessor index `e*(n+1)-1+k`. |
| T(z)_n=T_(n,en)z_n | `forward X e he`: the nth projection of the subsequence product followed by `X.asFunctor.map (homOfLE ...).op`. The inequality is supplied by existing Nat lemmas, without any sorry. |
| r_e induced by (b_e,a_e) | Simultaneous witnesses `res X` in `TransitionHomotopy`, pinned in every degree by `roosχ` and `biprod.map ((block ...).f p) ((selection ...).f (p+1))`. The product square `f ≫ b = a ≫ f_e` is also stated. These coordinates uniquely determine the chain map. |
| Delta induced by (T,T) | Simultaneous witnesses `delta X`, pinned in both coordinates by `biprod.map ((forward ...).f p) ((forward ...).f (p+1))`; the square `f_e ≫ T = T ≫ f` is stated too. |
| phi(x)_n=T_(n,en)x_en | `phi X e he := selection e X.asFunctor ≫ forward X e he`. After projection this is literally the displayed coordinate. |
| psi(y)_n=Σ_(en ≤ i < e(n+1)) T_(n,i)y_i | `psi X e he := block e X.asFunctor ≫ forward X e he`. Projecting and distributing composition over the finite sum gives T_(n,en)T_(en,i)=T_(n,i), exactly the specified formula. This uses the tower law, not a different map. |
| h(y)_n=Σ_(n ≤ i < en) T_(n,i)y_i | `telescope X e`, a product lift of `Finset.range (e*(n+1)-1-n)` with summand index `n+k`, followed by the transition from `n+k` to `n`. This is precisely the positive-level interval `[n+1,e*(n+1))`. |
| Delta r_e=(psi,phi) | `(res X ≫ delta X).f (p+1) ≫ (roosχ X p).hom = ... biprod.map ((psi ...).f p) ((phi ...).f (p+1))`. Lean composition runs left-to-right. |
| hf=1−phi | `roosU X ≫ telescope X e = 𝟙 _ - phi X e he`. |
| fh=1−psi | `telescope X e ≫ roosU X = 𝟙 _ - psi X e he`. |
| H(y,x)=(0,−hy), degree −1 | `H X : Homotopy (𝟙 ...) (res X ≫ delta X)` with its component `(p+2,p+1)` pinned, via source and target `roosχ`, to `biprod.lift 0 (-(biprod.fst ≫ (telescope ...).f (p+1)))`. As p ranges over ℤ this covers every adjacent pair; Homotopy.zero supplies zero at all other pairs. |
| dH+Hd=1−Delta r_e | The `Homotopy` binder itself states this: Mathlib's `comm` field is identity = dH+Hd+composite. The sign is negative in the second coordinate and the first coordinate is zero. |
| Delta quasi-isomorphism | `QuasiIso (delta X)`; the inverse restriction is also recorded as `QuasiIso (res X)`, as established in proof step 8. |
| [Delta]=[r_e]⁻¹ in derived category | An isomorphism `i : Q.obj R(K) ≅ Q.obj R(K^(e))` with `i.hom = Q.map (res X)` and `i.inv = Q.map (delta X)`. This is the exact inverse identity for the specified arrows. It avoids invoking `inv` before binding an IsIso instance. |
| All identities natural in strict tower maps | The witnesses res, delta and H are quantified simultaneously over X, followed by strict naturality equations for res, delta, selection, block, forward, telescope, phi, psi and all adjacent components of H. Nonadjacent components of H are zero by the Homotopy structure. |
| R a sheaf of commutative A-algebras | `R : Sheaf J RingCat`, `_algebra : underline A ⟶ R`, and sectionwise commutativity `_comm`. A ring-sheaf map from a commutative constant ring into a commutative ring sheaf is precisely the unital algebra structure in question. |
| Every displayed arrow/homotopy R-linear | The second conjunct repeats `TransitionHomotopy` in `ringedSiteModules R` itself. Every product projection, transition, finite sum, chain map and homotopy component is therefore an R-module-sheaf morphism. The same definitions specialize to that category, rather than choosing unrelated A-linear maps. |
| Same quasi-isomorphism and inverse identity in D(R) | The second conjunct includes the same QuasiIso and localized-isomorphism clauses in `DerivedCategory (ringedSiteModules R)`. It has its standard `HasDerivedCategory` size binder and no exact-products assumption for R-modules. |

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  definition and docstring (sheafification of the constant presheaf).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  full source and docstring; inherited `SheafOfModules.instAbelian` in Mathlib's
  `Algebra/Category/ModuleCat/Sheaf/Abelian.lean`, including its exact hypotheses.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, read in full, and their inverse-system functor interface.
  The delivered tower is directly such a functor, so no extra tower definition is used.
  This module is publicly available through the imported arithmetic infrastructure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, and the localization instance and
  quasi-isomorphism inversion signature, read at lines 70-110.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `HasProduct`, `piObj`, `Pi.π`,
  `Pi.lift`, `Pi.map`, read with full signatures and docstrings; countability uses
  `HasCountableProducts` from `Limits/Shapes/Countable.lean`.
- Added existing node `def-weil-strict-roos-model`: module
  `Sheaf.CategoryTheory.StrictRoosModel`, declarations `roosP`, `roosU`, `roosPmap`,
  `roosF`, `roosχ`, read in full. Reuses its exact signs and coordinate order.
- Added existing node `def-sp-strict-tower-arithmetic-restriction-data`: module
  `Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs`, declarations
  `StrictTowerArithmetic.index`, `complexRestriction`, `selection`, `block`, read
  in full. It already provides the exact positive arithmetic index and product maps.
- `Mathlib.Algebra.Homology.Homotopy`: full `Homotopy` signature, in particular
  the orientation of `comm` and the vanishing of nonadjacent components.

Searches run on 2026-10-21:

- msearch `leanfinder`, query "Finite block sums give a homotopy inverse to the
  forward subsequence transition on the Roos mapping fiber of an inverse tower of
  complexes": eight hits, including mapping-cone-composition and homotopy-cofiber
  homotopies, no assertion of these product formulas.
- msearch `loogle`, query `Homotopy, CochainComplex`: twelve hits, including
  `Homotopy.mkCoinductive`, `Cochain.equivHomotopy`, `Homotopy.shift`,
  `mappingCone.liftHomotopy` and `mappingCone.mapOfHomotopy`; useful infrastructure,
  no exact forward arithmetic transition statement.
- msearch `leansearch`, query "Finite telescoping sums on a subsequence of an
  inverse tower give chain homotopy equivalences between the mapping fibers of one
  minus shift": eight hits, including `Homotopy.shift`, `Homotopy.trans`,
  `mappingConeCompHomotopyEquiv`, `alternatingConstHomotopyEquiv` and
  `mappingCone.liftHomotopy`; no exact match.
- msearch `grep`, query `Roos|roos|subsequence.*homotopy`, subdirectory
  `Algebra/Homology`: zero Mathlib hits.
- Local rg in both project source roots for `Roos|roos|subsequence|Subsequence`
  found the existing strict Roos model, arithmetic maps, generic cofinal
  restriction, compact-support arithmetic restriction, and other Roos material.
  Opened the relevant modules: `StrictRoosModel`,
  `StrictTowerArithmeticRestrictionDefs`, `CofinalRoosRestriction`,
  `CompactSupportRoosCofinality`, `StrictRoosDerivedLimitComparison`,
  `RoosConeCalculus`, and upstream `Algebra/Homology/RoosComplex` and
  `CategoryTheory/Limits/TowerTransitionEndomorphism`.
- Local rg for this item's exact id in `lean/WeilConjectures` and in
  `dag/lean_names_upstream.json` found no existing binding. The generic cofinal
  theorem gives selection/block comparison, but does not specify this forward
  transition, negative telescoping homotopy, or inverse identity. The arithmetic
  maps and strict Roos object are reused instead of copied.

Edge cases checked by reading the finite formulas:

- e=1: q_e(n)=n; selection and forward are identities, block has one identity
  summand, telescope is the empty sum; phi=psi=1 and H=0. The two telescoping
  identities and both inverse equalities become the identity equations.
- e=2 and the first positive index: q_e(0)=1 and the homotopy's zeroth coordinate
  has precisely the transition from K_2 to K_1. The initial block is retained.
- Zero tower: all products, maps and homotopy components are zero, and the unique
  endomorphism is also the identity of the zero object.
- Zero transitions: forward is zero for e>1, so delta=0; the Roos fiber of f=1
  is contractible. No false termwise invertibility assertion is made.
- Arbitrary negative and positive cochain degrees are quantified by ℤ. The
  `(p+2,p+1)` homotopy formula covers every degree and needs no hidden `let`,
  `show ... from`, or implicit equality transport.
- Empty/degenerate site and zero coefficient ring are permitted: their module
  categories and formulas specialize to the trivial case. No nonemptiness,
  nonzero, boundedness, or characteristic hypothesis is imposed.
- No exactness of products is imposed in the R-algebra clause, consistently with
  node proof step 10. Countable products of module sheaves exist canonically.

Validation: scompile.py compiled the module in sandbox and library modes with
no errors or warnings. The initial compile diagnosed only an integer-degree
alignment and the use of `inv` before an IsIso instance was bound; the final
signature uses adjacent degree expressions and an isomorphism with both arrows
specified. No mathematical statement correction was needed. No disputed claim
or source error was found.

## Second reading by Q23

This is a second source-and-signature reading in this worker session; no other
agent was started, as the dispatch explicitly forbids it. The maintainer's
independent review remains the independent reader of the delivery.

I reopened the full node statement, ten proof steps, and the complete Lean file.
The site and ring binders form exactly the constant-module category, with the
recorded sheafification and Abelian interfaces. The tower is strict before
localization, all levels and all cochain degrees are present, and e is positive.
I checked the predecessor encoding separately for selection, the e-term block,
forward, and the half-open homotopy interval. No initial positive level is lost.
I checked composition order: Lean `res ≫ delta` is paper Delta r_e, and
`roosU ≫ telescope` is paper hf, while `telescope ≫ roosU` is paper fh.
The homotopy goes from identity to that composite and has coordinates (0,-hy),
so its `comm` field has exactly the stated sign. Its target coordinate degree
is p+1 when the source degree is p+2; ranging over p covers all integers.
The localized isomorphism fixes both images of the specified chain maps, so it
cannot be an unrelated cofinality isomorphism. I rechecked the last conjunct:
R is a commutative ring sheaf with the A-algebra map, and repeating the whole
predicate in its actual module category gives linearity as well as the D(R)
inverse identity, without assuming exact products there.

The rereading made naturality for selection, block and forward explicit as well
as naturality for res, delta, h, phi, psi and H. It also replaced the elementary
arithmetic proof block inside `forward` by existing Nat lemma terms. A clean
scompile.py run verifies the resulting file. No definitions were copied, no
node statement was corrected, and there are no new/dependency modules to audit.
