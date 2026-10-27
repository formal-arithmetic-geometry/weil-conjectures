## Worker report

The module `Sheaf.Paper.SupportedSourceSystemCupCalculus` renders the node unchanged.
It supplies the concrete product and concrete exact-pullback maps, and two theorems:
`SheafOfModules.supportedSourceSystemCupCalculus` (the three local laws) and
`SheafOfModules.supportedSourceSystemCupPullback` (the pullback law). Both proofs
are `sorry`; no data or definition is postponed. The helpers describe the owning
node's specified systems and maps, not independent notions or arbitrary replacements
for canonical constructions. No additional node or dependency repair is needed.

Hypothesis and clause mapping:

- The ringed site is `C`, `J`, `R : Sheaf J CommRingCat`; module sheaves are the
  recorded `ringedSiteModules` through `ShiftedModuleCategory R`. The sheafification
  and locally-bijective instances are those used by the recorded shifted-tensor
  interface to obtain the ordinary abelian module category. `u` and `v` are separate
  object and morphism universes; coefficients/modules use its `max u v` convention,
  while `w` is the independent derived-Hom universe. No equality of object and
  morphism universes is imposed. The label universes `l` and `l'` are independent.
- The derived category is the recorded `ShiftedDerivedCategory`; `T` is the recorded
  `ShiftedTensorModel R`, including its actual K-flat flat-term representative
  natural isomorphism, rather than an unconstrained tensor bifunctor.
- The set and its associative commutative operation are `A : Type l` and
  `[CommSemigroup A]`; multiplication denotes wedge. No unit, idempotence, or
  nonemptiness is assumed.
- `SupportedCupSystem.P` and `flatP` are the source sheaves and their flatness;
  `shiftedDegreeZero` places each sheaf in degree zero. `mu` is precisely the
  specified derived isomorphism. `mu_assoc` displays the canonical associator and
  transport along label associativity. `mu_comm` displays the canonical symmetry
  and transport along label commutativity.
- `L`, `flatL`, and `invertibleL` are the integer-indexed flat invertible ordinary
  sheaves. Invertibility is written as existence of an ordinary module sheaf M
  with L tensor M isomorphic to the ordinary unit; symmetry supplies the other
  side. This is an explicit hypothesis, not data chosen to construct a map.
  `h`, `h_assoc`, `h_comm` give the exact coefficient isomorphisms and their two
  coherence equations, including the integer-addition identifications.
- `supportedCup f g` is `(mu c d).inv` followed by the dependency's `shiftedTensorB`
  followed by `(shiftFunctor _ (a+b)).map (h r s).hom`. Its source is P(c*d) in
  degree zero and its target is L(r+s)[a+b], exactly the specified formula.
- The first two conjuncts of `supportedSourceSystemCupCalculus` are additivity in
  each variable. The third is associativity, with explicit transports from
  `(c*d)*e` to `c*(d*e)` and from the right to the left parenthesization of both
  weight and degree sums. The fourth is graded commutativity with scalar
  `(-1 : ℤ) ^ (a*b).natAbs` and the label, weight and shift-sum transports.
  NatAbs defines the same sign for negative integer exponents. All six weights
  and degrees `r,s,t,a,b,j` range over ℤ.
- The second ringed site and system are `C'`, `J'`, `S`, `TS`, `G`. The geometric
  morphism is `uInv ⊣ uPush` with finite-limit preserving inverse image, ring
  inverse-image datum `I` and ring map `ρ`. `U`, `hobj`, `hmap` specify exactly
  inverse image followed by scalar extension, on objects and maps. Additivity and
  finite-limit/finite-colimit preservation express exact module pullback. Its
  module right adjoint is `V`, `am`; this is the standard ringed-topos module
  adjunction used by the canonical comparison dependency, not a different functor.
- `κ` is the recorded pure-tensor-normalized ordinary comparison, including its
  defining generalized-element formula; `shiftedExactTensorPullback` is the
  recorded unique representative-normalized derived comparison. No arbitrary
  natural isomorphism is substituted for it.
- `φ : A →ₙ* B` is exactly the label map preserving wedge; it does not preserve a
  unit because none is assumed. `bP` and `τ` are the specified ordinary sheaf
  isomorphisms. `supportedCupSourcePullback` and `supportedCupWeightPullback` use
  the canonical degree-zero derived comparison and `singleFunctor.mapIso`.
- `hb` is the node's source multiplication compatibility equation, through the
  canonical tensor comparison, with `φ.map_mul` as the final label transport.
  `hτ` is exactly the coefficient multiplication compatibility equation.
- `supportedCupPullback f` is source-comparison inverse, U(f), the canonical
  shift comparison, and the shifted coefficient comparison. The concluding
  equality in `supportedSourceSystemCupPullback` is precisely U#(f star g) =
  U#f star' U#g, with the necessary `φ.map_mul` source identification. Both
  f and g range over the entire derived Hom sets, not representatives or
  cohomology classes restricted to pure tensors.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`;
  the signed total tensor is built into the recorded tensor presentation.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`, via `ShiftedTensorModel` and its
  published-model theorem.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`, `ShiftedTensorModel`,
  `shiftedDegreeZero`, `shiftedOrdinaryTensor`, `shiftedTensorB`,
  `derivedTensorAssociator`, `derivedTensorSymmetry`, `shiftedExactTensorPullback`,
  `shiftedTensorMorphismCalculus_local`, `shiftedTensorMorphismCalculus`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  and its public canonical ordinary comparison type. These give the normalization
  used by `shiftedExactTensorPullback`.
- Proof-only import `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`,
  especially normalized constraints, resolving tensor closure and additivity.

Sources checked: the full item statement and its four proof steps; all statement
dependency statements and Lean records; the recorded declarations' modules and
signatures/docstrings; Stacks `sites-cohomology.tex`, lemmas
`lemma-cup-product-associative` and `lemma-cup-product-commutative` (0FPL/0FPM);
current blueprint `main-20261015/.../sk-prop-an/lem-pur-frame-independence.proof.md`,
especially Permutations and Elementary shears. This is the node's source-system
assembly of shifted-Hom calculus; it does not claim the Stacks relative-cup
statements themselves literally have the source-system formulation.

Edge cases checked: empty labels (all quantified laws remain vacuous; no hidden
Nonempty), no identity or idempotence of wedge, repeated labels, zero source
sheaves and zero maps, integer degree/weight zero, negative degrees/weights,
odd/odd sign -1, even degree sign +1, zero coefficient ring and empty sites,
identity exact pullback, and noninjective/non-surjective label maps. All transports
were checked in the actual signatures; no dependent equality is suppressed by
replacing a canonical construction with a map parameter. No boundedness, positivity,
field characteristic, support idempotence or coefficient trivialization is added.
No statement correction or disputed assertion.

Searches for existing statements/notions:

- `msearch.py ... leanfinder` query: "Cup product of shifted derived morphisms with
  coherent flat source and invertible coefficient systems is additive associative
  graded commutative and compatible with exact pullback". Eight hits concern
  derived connecting morphisms and Ext composition; none gives this system calculus.
- `msearch.py ... loogle '"tensor", "shift"'`: OK, zero hits.
- `msearch.py ... grep 'cupProduct|cup_product|gradedComm'`: ten hits in Mathlib
  `LinearAlgebra/TensorProduct/Graded`, concerning graded modules, not ringed-site
  source-system derived morphisms.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `cupProduct|supportedSource|SourceSystem`: upstream `Etale.cupProduct` concerns
  the tensor unit and constant coefficients, and projection-formula cup products
  concern adjunctions. None states this flat source/coefficient-system theorem.
- `grep -rn 'lem-pur-supported-source-system-cup-calculus'
  lean/WeilConjectures`: no attachment. `rg` for the seven new declaration names
  in the project and upstream-name index: no existing name.
- Searched ordinary invertibility in Mathlib monoidal categories and the project's
  module-sheaf modules. The available scheme invertible-module predicates require
  schemes; the general site's ordinary tensor-inverse condition is spelled out
  directly in the owning system hypothesis, without a duplicate predicate.

Validation: prescribed scompile.py compiled the file as sandbox and as its real
library module with exit 0 and no warnings. Two theorem sorry bodies are the only
postponed work. Final dry-run compilation will also check the explicit dependency
imports added for the stage-3 proof plan.

## Second reading by Q21

The dispatcher forbids spawning another agent; this is a second in-thread reading,
not a claimed independent review. The maintainer's independent delivery review
remains required. I reopened the node and final module and matched every hypothesis
and conclusion as above. I checked the source/target of each transport: the local
associative RHS begins at P((c*d)*e), ends at L((r+s)+t)[(a+b)+j], and the signed
RHS begins at P(c*d), ends at L(r+s)[a+b]. The pullback RHS begins at G.P(φ(c*d))
and is transported to G.P(φ(c)*φ(d)); both maps then end at G.L(r+s)[a+b].
The first compile found a namespace collision between two canonical-comparison
types; qualifying `CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison`
fixes it while retaining separate site universes. No mathematical clause changed.
Both theorem proofs remain sorry, and every helper is a concrete structure or map.
