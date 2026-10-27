## Worker report

Item: lem-trf-toric-chart-fs-realization. Module:
`Sheaf.AlgebraicGeometry.ToricChartFSRealization`.
Main declaration: `AlgebraicGeometry.toricChart_fs_realization`.
Its proof is exactly `by sorry`; nothing is proved in this delivery.
The helper `AlgebraicGeometry.toricTensorGlobalChart` is a real composite of the
canonical monomial homomorphism with the inverse affine global-sections isomorphism.
No object is chosen from an existence theorem.

Clause-by-clause comparison with the unchanged node statement:

- A commutative ring A: `(A : Type u) [CommRing A]`.
- The locally Noetherian affine base Y: `[IsLocallyNoetherian (Spec (.of A))]`.
- Fine saturated commutative monoids P,Q: `(P Q : Type u) [CommMonoid P]
  [CommMonoid Q]` and `_hP : IsFineSaturatedMonoid P`, `_hQ : IsFineSaturatedMonoid Q`.
  These are the recorded fs predicates, including finite generation, injection into
  the canonical group completion, and saturation. Multiplicative notation simply
  renames additive zero and addition as one and multiplication; it imposes no extra
  torsion-free or sharpness assumption.
- Any monoid homomorphism g and structural homomorphism alpha: `(g : P →* Q)` and
  `(α : P →* A)`. No injectivity, saturation of g, or log regularity is assumed.
- Z[P] and Z[Q], with the prescribed scalar maps and tensor multiplication: the
  already-landed `logIdealTensorRing A α g` is literally
  `TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)` using
  `(MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra` and
  `(MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra`. Its commutative ring instance is
  the usual `Algebra.TensorProduct` ring structure, with pure tensor product
  `(a ⊗ u)(b ⊗ v) = ab ⊗ uv`. `logIdealTensorBase A α g` is includeLeftRingHom,
  hence a maps to a tensor 1. No alternative model of C is introduced.
- Every finite generating tuple, including length zero: `∀ (r : ℕ) (q : Fin r → Q),
  Submonoid.closure (Set.range q) = ⊤ → ...`. This quantifies every tuple, rather
  than choosing one tuple or only claiming finite type.
- The evaluation map and its surjectivity: `Function.Surjective
  (MvPolynomial.eval₂Hom (logIdealTensorBase A α g)
  (fun i ↦ logIdealTensorMonomial A α g (q i)))`. The ring hom uses exactly the
  canonical A coefficient map, and therefore is evaluation as an A-algebra map.
- C Noetherian: `IsNoetherianRing (logIdealTensorRing A α g)`.
- X = Spec C locally Noetherian: `IsLocallyNoetherian
  (Spec (.of (logIdealTensorRing A α g)))`.
- beta is the canonical monomial map: `logIdealTensorMonomial A α g` is
  includeRight composed with `MonoidAlgebra.of ℤ Q`. `toricTensorGlobalChart`
  transports this beta into Γ(Spec C,top) through `Scheme.ΓSpecIso.inv`.
- Existence of the associated log structure, with its canonical sheafification map:
  the existential L and eta, followed by `IsAssociatedLogPresentation.{0,u}
  (toricTensorGlobalChart A α g) L η`. This is the recorded quotient-pair
  sheafification universal property and structure formula, so L is specifically
  the associated structure, rather than an arbitrary log structure with a chart.
- The canonical map Q → L(X) is a global chart: `L.IsChart` at
  `Scheme.Etale.mk (𝟙 (Spec C))`, applied to `associatedLogIota` precomposed with
  `MulEquiv.ulift.symm.toMonoidHom`. The precomposition simply undoes the dependency
  API's ULift; the chart domain is Q itself. No independent chart is existentially
  chosen. The universe arguments `{0,u}` keep the dependency's lift in Type u.
- The structural image equals beta: equality of the structural component composed
  with that same canonical chart and `toricTensorGlobalChart A α g`. This is the
  affine global-sections rendering of exactly q maps to 1 tensor z^q.
- The log scheme is fs: `L.IsFineSaturated`, together with the explicit local
  Noetherianity conclusion, is exactly the data of `FineSaturatedLogScheme` on X.
- Zero C is allowed: there is no Nontrivial, domain, or nonempty-scheme binder.
  There is no base log structure, log regularity, or hidden map condition.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and the affine
  spectrum convention. `Scheme.ΓSpecIso` supplies the standard affine identification.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and
  `IsLocallyNoetherian.component_noetherian`; the affine cover equivalence is the
  recorded pqf-def-locnoeth/pqf-lem-affine-open-locnoeth interface.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`, `IsChart`,
  `IsFineSaturated`, and the imported `IsFineSaturatedMonoid` defined in
  `Sheaf.AlgebraicGeometry.LogRegularPair`. Read their full definitions and docstrings.
- `Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`:
  `associatedLogPresheaf`, `IsAssociatedLogPresentation`, `associatedLogIota`, and
  the theorem `associatedLog_universal_stalks`. The canonical pair formula and
  geometric pushout conclusion supply exactly the associated global chart.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`: `logIdealTensorRing`,
  `logIdealTensorRing.commRing`, `logIdealTensorBase`, `logIdealTensorMonomial`.
  The existing node def-trf-log-ideal-chart-presentation is added to stmt_deps,
  as explicitly authorized for reusing a landed definition node. Its other data
  is untouched; no new definition node or dependency replacement is necessary.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `Mathlib.RingTheory.TensorProduct.Basic`:
  `TensorProduct`, its balanced quotient and multiplication; available through the
  tensor-ring module, so there is no duplicate tensor construction.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `eval₂Hom`,
  and the recorded `aeval` universal-property interface. eval₂Hom uses the explicit
  coefficient ring map because the existing tensor interface exposes that map.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- Proof-only import `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`,
  `Algebra.FiniteType`, and `Algebra.FiniteType.isNoetherianRing`, for the recorded
  finite-type and Noetherian proof dependencies.

Source check: read ILO VI 1.1 (printed p.69) in the local PDF: étale charts by fs
monoids and locally Noetherian convention. Read VIII 3.3.3--3.3.11 (printed
pp.107--108): monoid algebras, chart realization and chart base change. Read
Stacks algebra.tex lemma-Noetherian-permanence (00FN) and properties.tex
definition-noetherian / lemma-locally-Noetherian (01OV/01OW). The latest blueprint
search `python3 tools/blueprint_refs.py search 'toric chart'` returns no matching
blueprint unit; the node records this as a retained helper of the older alteration
route. It is not the unit's own statement, and no source correction is needed.

Edge cases checked mathematically before writing:

- r=0: closure of the empty tuple is the identity submonoid, so generation means
  Q is trivial. Evaluation from zero-variable polynomials is still meaningful.
- Q a group, for instance Z with generators +1,-1: the tuple may include inverse
  elements, and ordinary nonnegative polynomial powers still generate the tensor
  algebra. Saturated monoids are not inadvertently required to be sharp.
- Unit torsion is allowed by the recorded fs predicate; no affine-monoid
  torsion-free class is used.
- C=0 with A nonzero, e.g. P=N, Q=Z and alpha(1)=0: making that monomial invertible
  yields the zero ring. No theorem binder excludes it; its empty spectrum has no
  geometric-point chart obligations. A=0 is allowed as well.
- P=Q and g=id: C is the usual base A and the original associated chart is recovered.
- g arbitrary and possibly noninjective: mapDomainRingHom and the tensor ring
  handle it directly; no submonoid-of-group-completion specialization is used.

Searches for existing declarations (2026-10-24):

1. msearch.py leanfinder: "For fine saturated monoids P and Q, the toric chart
   tensor product A over Z[P] with Z[Q] is Noetherian and has an associated fine
   saturated log structure". Eight hits, including `Algebra.EssFiniteType.isNoetherianRing`
   and ordinary finite-type/localization lemmas; no full logarithmic realization.
2. msearch.py leansearch: "A monoid chart on an affine scheme determines a fine
   saturated logarithmic structure". Eight hits, including `IsAffineMonoid.toFG`
   and affine-scheme constructors; no associated-log realization theorem.
3. msearch.py loogle: "AddMonoidAlgebra.lift, AddMonoidAlgebra.mapDomainRingHom,
   Algebra.TensorProduct.includeRight". Zero hits for the combined query; direct
   source reads found the existing individual monoid-algebra and tensor interfaces.
4. msearch.py grep: `toric|Toric|LogStructure` in AlgebraicGeometry: zero Mathlib hits.
5. rg over Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json for
   `ToricChartFSRealization|toricTensorGlobalChart|toricChart_fs_realization`: no
   collision. rg for the item id in upstream WeilConjectures found none.
6. rg for `logIdealTensorRing`, chart/log-structure names and toric charts in the
   project found LogIdealChartPresentation's generic tensor ring and reused it.
   `AlgebraicGeometry.toricChartRing` in the parent LogRegularToricRefinement module requires Q to be a
   submonoid of P's group completion, and its theorem assumes a log regular base;
   it cannot state this node's arbitrary g or its polynomial-surjectivity clause.
7. DAG search for the generic tensor construction identifies the existing
   def-trf-log-ideal-chart-presentation node. No new notion node is required.

No STATEMENT-DISPUTED issue or statement correction. Only lean and the authorized
addition of a landed definition node to stmt_deps change in the item copy.

Validation: scompile.py Q75 lem-trf-toric-chart-fs-realization on the module passed
both sandbox and library checks with no errors or warnings. Final delivery checks
also compile the delivered file, including its final documentation.

## Second reading by Q75

Performed a separate second pass with the node statement, its four proof steps,
the delivered module, and the dependency definitions open. The dispatcher explicitly
prohibits starting other agents; this is a worker self-check, with the maintainer's
independent review to follow.

The opening binders match A, its locally Noetherian spectrum, the two fs monoids,
and arbitrary g and alpha. The first conjunct quantifies every generating Fin r
tuple and fixes coefficient and variable evaluations correctly. The next two
conjuncts are Noetherianity of the actual tensor ring and local Noetherianity of
its spectrum. The final existential retains the canonical quotient presheaf,
sheafification presentation, canonical map from pairs, chart test, exact structural
map, and fs condition. Read the ULift down/up maps to confirm the chart really has
source Q. The global-sections transport uses ΓSpecIso.inv, in the correct direction
from C to Γ(Spec C,top). Checked the empty tuple, zero tensor ring, group units and
arbitrary noninjective g cases against every binder. No missing hypothesis or extra
conclusion was found. Reused the already generic tensor ring rather than the
specialized parent toric-refinement definition; the only DAG addition is the
owning landed definition node in stmt_deps. No mathematical change was necessary
on this second pass.
