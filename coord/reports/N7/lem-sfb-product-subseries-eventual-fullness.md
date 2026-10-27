## Worker report

The module `Sheaf.AlgebraicGeometry.ProductSubseriesEventualFullness` states
`AlgebraicGeometry.Scheme.Modules.product_subseries_eventual_fullness` with a single
`sorry`. All five helper declarations have real bodies; no existence theorem is used
to choose data. They belong to the product-series notion of this item, as permitted by
the human's same-module helper authorization. The required fieldSections extraction has landed as a shared-library maintenance
repair at 1b012d88fc2bfacca5b951add453c9e40c1092d0. This consumer packet uses that
landed definition; there is no statement correction or disputed statement.

Source checked: Morrison, arXiv:0810.2340, Section 2.3, printed p.9, equation (4) and
its pointwise justification, https://arxiv.org/pdf/0810.2340, PDF page 9. The passage
asserts that the product subseries is very ample and base point free, its high
symmetric powers fill the target sections, and Riemann--Roch gives the dimension.
This delivery states the pointwise assertion only. The displayed target in the PDF's
last explanatory sentence suppresses the nth tensor power; its preceding sentence,
formula (4), and this DAG node specify that power unambiguously.

Hypotheses and clauses:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The curve and its structure morphism are `(C : Scheme.{u}) [C.Over (Spec (.of k))]`.
  `IsConnectedCurve (C ↘ Spec (.of k))` includes finite type, separatedness,
  connectedness, nonemptiness, and dimension exactly one. `Smooth` and `IsHProjective`
  on this same morphism render smoothness and projectivity, respectively.
- `(L A B : C.Modules)` and their three `IsInvertible` instances are the three
  invertible structure modules. The numeric names d,a,b are expanded by their
  defining expressions `L.degree k`, `A.degree k`, `B.degree k`. The genus g is
  expanded to the recorded `C.arithmeticGenus k`. No extra hypotheses on these
  numeric names are needed.
- `V`, `U`, `T` are `Submodule k (ProjectiveSpace.fieldSections k ...)`, using the
  existing restriction of scalars on actual global sections. Their three
  `FiniteDimensional` instances and `hV`, `hU`, `hT` express finite dimension
  and nonzero subspaces. None is required to equal the full space of sections.
- `subseriesEvaluation` is the free-sheaf map whose generating family consists
  of all elements of the subspace, each made into a compatible section by
  `unitHomEquiv (homOfGlobalSection ...)`. `hVe`, `hUe`, `hTe` say these maps
  are epi. Their image is exactly the image of the usual evaluation
  `V tensor_k O_C -> L`: at a stalk both images are the O_C-span of the same
  vectors. Thus this expresses precisely the node's evaluation surjectivity.
- `hVemb : IsEmbeddingSubseries k L V` uses a finite basis of V and the existing
  `ProjectiveSpace.homOfGeneratingSections`. The map is the canonical map from
  the actual basis sections, rather than an arbitrary embedding. Projective
  space with these basis coordinates identifies with P(V dual). Basis change
  is a projective automorphism, so the existential basis adds no hypothesis.
- `(p l : ℕ) (hl : l ≤ p)` expresses the nonnegative integers and 0 <= l <= p.
  `productSeriesLine L A B p l` is `(L tensor A^(p-l)) tensor B^l`.
  It is a transparent abbreviation so existing invertibility instances apply.
  `seriesTensorProduct` recursively tensors arbitrary lists of sections; its
  zero branch is `unitSectionsEquiv ... 1`, and its successor branch is
  `tmulSection`. `productSubseries` is the k-span of exactly the products with
  one v, p-l independently chosen u's and l independently chosen t's.
- The first conjunct is epi evaluation for this actual S and actual M.
  The second is `IsEmbeddingSubseries` for this same pair, hence the claimed
  canonical closed immersion by S, not just very ampleness of its line.
- `exists n₀ : ℕ, forall n : ℕ, n₀ ≤ n -> ...` is eventual fullness; n₀ lies
  after every datum and both exponents in the quantifier order. Using natural
  indices is equivalent to the node's nonnegative tensor exponents and an
  integer bound: replace a bound by its maximum with zero.
- The symmetric power is Mathlib's `SymmetricPower k (ULift.{u} (Fin n)) S`.
  ULift puts the finite index in the field universe, as required by Mathlib;
  its index equivalence with Fin n makes it precisely Sym^n_k S, without
  restricting the field universe.
- The conclusion supplies a k-linear `μ` into the existing vector space of
  sections of M^n, and explicitly requires its value on EVERY pure symmetric
  tensor to equal the recursively constructed product of its factors.
  `SymmetricPower.span_tprod_eq_top` says these tensors span, so the equation
  uniquely determines μ as multiplication. Its existential presentation does
  not replace multiplication by an arbitrary surjection, introduce any extra
  assumption, or choose a noncanonical map from a mere existence axiom.
  It is the property of the canonical multiplication map stated directly.
- `Function.Surjective μ` is eventual surjectivity. The integer-cast
  `Module.finrank k (LinearMap.range μ)` is the dimension of its actual image;
  its right-hand side is exactly n(d+(p-l)a+lb)+1-g. Integer arithmetic
  preserves the subtraction in the formula, avoiding truncated subtraction.
- There is no characteristic restriction, degree-one surjectivity assumption,
  completeness assumption, or uniform bound over varying data.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the mathematical field structure).
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, and the existing scheme module tensor.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `Scheme.arithmeticGenus`, `Scheme.Modules.degree` (exact recorded genus/degree).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.globalSectionsFunctor`, `RingedSpace.moduleCohomology`.
  Global sections here are literal section modules. The genus/degree use their
  prescribed existing definitions; no new cohomology construction is supplied.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; the scheme tensor specializes the same
  existing sheafification/localization construction. No private tensor is introduced.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`:
  `tmulSection`, `unitSectionsEquiv`; `Modules.PullbackFreeGenerator`:
  `homOfGlobalSection`; Mathlib sheaf modules: `unitHomEquiv`, `freeHomEquiv`.
- `Sheaf.AlgebraicGeometry.FieldGlobalSections`: `ProjectiveSpace.fieldSections`.
  The landed definition node `def-sfb-field-global-sections` owns this unchanged
  definition. The item cites this definition node, replacing the previously
  proposed theorem-node dependency. The product-series module directly imports
  the landed definition module.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `ProjectiveSpace.homOfGeneratingSections`. Its owning definition node is added
  to stmt_deps (it was already a proof dependency).
- `Mathlib.LinearAlgebra.TensorPower.Symmetric`: `SymmetricPower`, `tprod`.

All recorded proof-dependency modules are imported privately unless their interface
is used in the public statement. The theorem docstring gives all five proof steps:
fibrewise generation; point/tangent separation; restriction and coordinate-monomial
identification; Serre vanishing; degree additivity and Riemann--Roch.

Edge cases checked before drafting and on rereading: p=l=0 gives L up to unitors
and S=V under that canonical identification. l=0 and l=p omit exactly the absent
factors. All Fin 0 products return the unit one. The symmetric tensor formula
also has its correct degree-zero empty product, though the eventual bound need
not include n=0. Dimension and generation do not require characteristic zero;
there is no division by factorials. Nonzero subspaces may have dimension one
(e.g. the generated auxiliary trivial line). A one-dimensional embedding series
cannot occur on the required connected dimension-one curve, but the definitions
still treat projective dimension zero correctly. Empty and disconnected schemes
are excluded by the node itself through IsConnectedCurve, not by added binders.

Searches (msearch.py, group N7, this item):

- LeanFinder: `A very ample linear series multiplied by generated linear series has
  eventually surjective symmetric powers` returned eight hits (Proj localization
  surjectivity, SymmetricPower spanning, unrelated SymAlg facts), no exact match.
- Loogle: `SymmetricPower, Submodule.span, LinearMap.range` returned zero hits.
- Mathlib grep: `productSubseries|eventual.*[Ss]urject|symmetricPower` in
  AlgebraicGeometry returned zero hits.
- LeanSearch: `product linear series tensor product sections symmetric power
  multiplication line bundle` returned the existing SymmetricPower and general
  tensor multiplication APIs, no product-series eventual-completeness theorem.
- Mathlib grep: `productSubseries|IsVeryAmpleSeries|IsSectionMultiplication|tensorProductSection`
  returned zero hits. The same rg pattern on dag/nodes, WeilConjectures and Sheaf
  returned zero hits. Wider source/project searches for linear series and
  symmetric powers found MovingLinearSeriesZero (restriction), the canonical
  fieldSections interface, the section-ring constructions, and projective
  polarization (used as a proof dependency), not this statement. Searching the
  item's id in WeilConjectures returned no declaration. Blueprint_refs ancestor
  reports null; its product-subseries search returned no existing notion to reuse.

Validation of the repaired packet: scompile.py compiled all three affected files
separately against the live server in dependency order, including under their actual
library names, with no errors or warnings. FieldGlobalSections took 6.1 seconds,
ProductSubseriesEventualFullness 3.5 seconds, and MRegularConsequences 2.9 seconds.
The original theorem signature and all its helper bodies are unchanged.

## Repair of return H2

The independent return on immutable head 0e5b17a239f5 requires the plain
ProjectiveSpace.fieldSections definition to have a definition-node owner, rather
than using the unrelated regularity theorem as a statement prerequisite.

Maintenance commit 1b012d88fc2bfacca5b951add453c9e40c1092d0 on sheaf-dag now
provides def-sfb-field-global-sections and Sheaf.AlgebraicGeometry.FieldGlobalSections.
It moves the exact existing definition, including its full name, signature and body.
MRegularConsequences publicly imports it, removes its local copy, and cites the
new definition in its own statement dependencies. The old theorem signature and
proof are unchanged; there is exactly one definition.

This separate maintenance extraction resolves a genuine preflight ownership
conflict: once the consumer dropped the regularity theorem dependency as required,
the old owner's module could no longer be edited in the consumer delivery.
No pipeline check or landing tool was changed. The already-landed definition and
old-owner node/module copies were removed from this sandbox's delivery inputs;
all four former files and this report have .bak copies. The packet now consists
only of the product-series module, its item node and this report.

The item cites the landed def-sfb-field-global-sections and the landed projective
map definition. It imports FieldGlobalSections directly; it has no spurious
regularity-theorem dependency. The consumer theorem, helper bodies, five-step
proof plan and natural-language node statement are unchanged from the reviewed
packet. The next worker should retain this reduced packet and run the normal
deliver2.py dry-run/delivery commands. No new node or dependency-module repair
is part of the consumer delivery now.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
