## Worker report

The module Sheaf.Paper.CoefficientFiniteDescentObjects states
AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects, with one sorry and no
new definitions. The node is unchanged except for lean. No statement correction,
new nodes, dependency repairs, or STATEMENT-DISPUTED issues are needed.

Hypothesis and clause correspondence:

- The standing field is `(k : Type u) [Field k] (p ℓ : ℕ) [CharP k p]`,
  `(_hp : 0 < p)`, `(_hpℓ : p ≠ ℓ)`, and `[Fact ℓ.Prime]`. Positive
  characteristic is stated directly, without imposing a redundant additional prime
  hypothesis on p. Schemes use `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact (X ↘ Spec (.of k))]`,
  and `[IsSeparated (X ↘ Spec (.of k))]`. These are precisely separated finite
  type over k. No additional Noetherian or geometric assumption is imposed.
- The fixed closure is `PadicAlgCl ℓ`. Finite fields throughout are the recorded
  `Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)`, definitionally the same subtype
  as `PadicAlgCl.FiniteIntermediateField ℓ`, not arbitrary abstract finite fields.
  The subtype's order `E ≤ F` is inclusion of the intermediate fields.
- Dbc(X,Qlbar) is `ConstantModelBoundedConstructible
  (Profinite.padicAlgClRingObj ℓ) X`; Dbc(X,E) is
  `ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X`.
  These are the finite constant local model definitions imported through the
  recorded det-def-sfb-constructible-tor-amplitude module. Their objects have
  canonical t-structure boundedness and constructible cohomology in every degree.
  This is not the different upstream local-presentation constructibility notion.
- The first conjunct universally quantifies K, then asserts existence of E and
  K_E in the stated full subcategory, together with
  `Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)`.
  The isomorphism is in the ambient unbounded derived category, as required.
- The second conjunct universally quantifies K, E and every bounded constructible
  K_E. The same `Nonempty` isomorphism is the model hypothesis. It then quantifies
  every finite F with `h : E ≤ F`. Its first conclusion is
  `constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
  ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj)`. Its second conclusion is
  `Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj
  ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ≅ K.obj)`.
  Both the constructibility and the model isomorphism are therefore explicit.
- The functors are the recorded `derivedExtendScalarsSubfield` and
  `derivedExtendScalarsToPadicAlgCl`, on internal module-object unbounded derived
  categories over `padicSubfieldRingObj` and `padicAlgClRingObj`. Their rings are
  definitionally `condensedRingObj (Profinite.continuousMapRingObj E) X` and
  `condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`. Thus the tensors use the
  specified condensed inclusions, with no discrete-coefficient replacement.

Statement dependency declarations read and used:

- sk-def-sfb-dc-setting: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.
  BoundedConstructible, `AlgebraicGeometry.ProEtale.CondensedRing.
  compactificationOverField`. The setting is rendered by explicit binders,
  following the node's record; this object-only assertion needs no chosen
  compactification as an additional argument.
- det-def-sfb-constructible-tor-amplitude: Sheaf.Paper.ConstantModelTorAmplitude,
  `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`;
  it publicly imports Sheaf.Paper.CondensedConstantConstructibility, which owns
  `ConstantModelBoundedConstructible` and `constantModelBoundedConstructible`.
  Their complete bodies and the supporting local-model definitions were read.
- def-weil-finite-subextension-directed-set:
  Sheaf.NumberTheory.Padics.FiniteCoefficientFields,
  `Padic.FiniteCoefficientFields`, including its subtype body and order.
- def-sfb-derived-extend-subfield and def-sfb-derived-extend-to-qlbar:
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit,
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsSubfield` and
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsToPadicAlgCl`. The full
  signatures and docstrings were read in the prescribed framework checkout,
  and the current source was also inspected with scompile.py --source. Its
  `finiteCoefficientDerivedExtension` and `finiteCoefficientDerivedToAlgCl`
  abbreviations retain exactly the same L(Ext) coefficient maps.

Available proof dependency modules are imported, including the recorded Hom
and lisse descent modules, exact-derived-factorization, Noetherianity and triangle
isomorphism modules. TwoColimit publicly provides the flatness and transitivity
modules. The currently unrecorded triangulated-closure, finite-generation and
scalar-six-pullback proof nodes have no module to import; no definition from
those nodes is needed to type this assertion. Their exact uses are retained in
the five-step proof docstring. The general change-of-scalars module is already
in the public dependency closure; it has no separate lean record here.

Source read: the current main-20261015 objects-descent statement and proof, plus
the DAG's five-step expansion. The docstring includes the preliminary Noetherian
check, persistence and shifts, descent of the connecting map at shift 1, both
inverse rotations with unchanged connecting sign, locally closed generators
including the closed factor, and the finite induction with a zero model.

Edge cases checked before drafting: X may be empty; K and K_E may be zero;
rank-zero generators and empty stratifications are not excluded. F may equal
E, including the bottom intermediate field representing Q_l. All complexes,
shifts and cohomological bounds allowed by Dbc remain quantified: no degree,
rank, Tor-amplitude or connectedness restriction is added. All characteristics
p > 0 distinct from ℓ, all primes ℓ, and every scheme universe u are included.
The site retains its original object/morphism universes and Ab.{u+1}; no
universe equality or smallness hypothesis is added.

Searches (2026-10-18), all using the prescribed tools/paths:

- msearch.py LeanFinder: "Bounded constructible derived pro-etale sheaves over
  algebraic closure of l-adic numbers descend to a finite coefficient field
  extension". Eight hits, including BDeRham, BDeRhamPlus and étale algebra
  descent; none concerns this assertion.
- msearch.py Loogle: `"Constructible", "extendScalars"`: zero hits.
- msearch.py LeanSearch: "Bounded constructible complexes over algebraic closure
  of l-adic numbers descend to a finite extension". Eight hits, including
  PadicAlgCl, PadicComplex and bounded derived representatives; no match.
- msearch.py Mathlib grep:
  `constructible.*(descent|scalar)|finite.*descent.*complex`: zero hits.
- rg on WeilConjectures and lean/Sheaf for
  `coefficient_finite_descent_objects|finite.*descent.*[Oo]bject|constructibleCocone_essSurjObj`,
  plus the item's exact id upstream: no existing full statement. A broader
  case-insensitive finite-descent search found unrelated scheme descent and
  existing lisse/Hom descent modules.
- Inspected the prescribed framework's TwoColimit module: its
  `constructibleCocone_essSurjObj` uses the upstream BoundedConstructible notion,
  and does not include this node's persistence clause. It is not an exact match.
  Inspected Sheaf.Paper.FiniteCoefficientDescentTwoColimit: the unit theorem
  includes object existence as one conjunct among several statements, but does
  not state the persistence clause. It explicitly uses this item in its proof
  plan, so importing the consumer here would also reverse the intended route.

Validation: scompile.py Q10 det-lem-coefficient-finite-descent-objects compiled
this file as a sandbox and under its library module path with no errors and no
warnings (4.4 s for the library-path compile). All binders and universes are
explicit; `set_option autoImplicit false` is in the file. There are no hollow
definitions and the sole proof is sorry, as required for stage 2.

## Second reading by Q10

This is the author's direct-delivery self-check, not an independent-agent review;
the dispatch brief forbids spawning agents and assigns independent review to
the maintainer. I reopened the JSON and the final Lean declaration. Each standing
hypothesis appears in the binders. The coefficient-field subtype is the recorded
one and unfolds to the upstream indexing type. Both Dbc binders use the finite
constant local model convention. The first conjunct has the correct existence
quantifiers and ambient isomorphism. The second applies to every model, every
finite enlargement including equality, and states both required conclusions.
I checked that both iterated functor applications use the exact same F and h.
No mismatch remained and no natural statement changed. The only drafting fix
was removing an extra leading space in the module docstring. The maintainer's
independent reading remains the subsequent review gate.
