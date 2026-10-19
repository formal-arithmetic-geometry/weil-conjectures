## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.NormalApproximationFiniteEtaModification`
states `AlgebraicGeometry.exists_normal_noetherian_model_of_finite_eta_modification`.
The only theorem proof is `sorry`; there are no definitions or new nodes. The node is
unchanged outside `lean`. The complete eleven-step natural-language DAG proof is in
the theorem docstring, including the finite algebra / base-torsion quotient argument
which avoids assuming that the original finite morphism is finitely presented.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes are `{S Z Z' : Scheme.{u}}`; `p : Z ⟶ S`, `f : Z' ⟶ Z`.
  The source has its induced structure map `f ≫ p`; no unrelated structure map is chosen.
- The affine integral base is `[IsAffine S] [IsIntegral S]`. Normality is
  `hS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s)`; integral schemes already
  have domain stalks, so this says every local ring is an integrally closed domain.
- Flatness is `[Flat p]`. Finite presentation is the complete combination
  `[LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]`.
- Reduced geometric fibres are `[GeometricallyReduced p]`. Mathlib quantifies over
  all field-valued points; this is equivalent to reducedness after algebraic closure
  of each residue field, by faithfully flat field extension and base change of a
  geometrically reduced algebra. It uses the same scheme pullbacks as the fibre node.
- `η : S` and `hη : IsGenericPoint η Set.univ` name the generic point. Integrality
  makes it unique; the theorem does not require a preselected choice of that point.
- Finiteness is `[IsFinite f]`; the properness required in the node's definition of
  modification is included explicitly as `[IsProper f]`.
- `hfη` says that the induced map after `Over.pullback (S.fromSpecResidueField η)`
  is an isomorphism. `Over.homMk f rfl` is the original morphism over S, with source
  `Over.mk (f ≫ p)` and target `Over.mk p`; the functor constructs its canonical map.
- `hf` supplies the target open V. `∀ W, Function.Injective (V.ι.app W)` is precisely
  injectivity of `O_Z → j_* O_V` on every open W. The next conjunct is the same
  condition on the inverse-image open of Z'. `IsIso (pullback.snd f V.ι)` says f
  is an isomorphism over V. These conditions are expanded inside the theorem,
  rather than introducing a duplicate named definition. The only existing
  `MultipointedCurve.Hom.IsEtaModification` applies to curves and markings, not
  to the arbitrary family in this node.
- The conclusion supplies `S₀ Z₀ Z'₀`, `q`, `p₀`, `f₀`, and `η₀`. The conjuncts
  `IsAffine S₀`, `IsIntegral S₀`, `IsNoetherian S₀`, and the local-ring domain and
  integral-closure conditions give exactly the base requested. Mathlib's
  `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`: the definition
  of Noetherian specified in the node, using Noetherian affine coordinate rings.
- `IsDominant q`, `IsGenericPoint η₀ Set.univ`, and `q η = η₀` record dominance
  and the specified behavior on generic points.
- `Flat p₀`, `LocallyOfFinitePresentation p₀`, `QuasiCompact p₀`,
  `QuasiSeparated p₀`, and `GeometricallyReduced p₀` retain every family property.
- `IsFinite f₀`, `IsProper f₀`, the generic-fibre `IsIso` condition and the open V₀
  with both sectionwise injectivity conditions repeat exactly the modification
  clauses for the model.
- `e : Z ≅ pullback p₀ q` and `e' : Z' ≅ pullback (f₀ ≫ p₀) q` are the two
  base-change isomorphisms. The equation `e.hom ≫ pullback.snd p₀ q = p` says e is
  over S. The last equation says that e' intertwines f with the canonical base
  change of f₀. Together they also imply that e' is over S, by composing that
  equation with the second projection and using the functor's projection identity.
  Thus no compatibility with the structure maps has been omitted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, including
  its nonempty condition and domain sections on all nonempty opens.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`; its docstring
  states equivalence of the affine-section definition with stalkwise flatness.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` plus quasi-compactness and
  quasi-separatedness for the global finite-presentation condition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, and its projections. The geometric-fibre node's
  recorded declaration is the pullback itself, as used by the canonical base changes.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented scheme
  base change uses `Over.pullback`, with the induced morphism the functor's map;
  `AlgebraicGeometry.baseChange_morphism_projections` records precisely the two
  projection equations used for the compatibility explanation above. The old
  checkout lacks this module, so its complete current source was read through
  `scompile.py --source WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the scheme counterpart
  used in the conclusion is `AlgebraicGeometry.IsNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`, whose full fields were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.

All recorded non-Mathlib proof-dependency modules are imported without `public`;
statement dependencies are public imports. The geometric-fibre limit descent,
generic-fibre smoothness and affine-open finite-presentation nodes do not yet have
recorded modules and hence cannot have proof imports here. No proof prerequisite
was substituted for a hypothesis of this theorem. No missing statement interface
required a dependency repair.

Source: Temkin, arXiv:0707.3953v3, Proposition 3.5.2, printed p. 20 (PDF page 20),
noetherian-reduction paragraph; §3.1 and Remark 3.1.1(i), printed p. 14.
Read at https://arxiv.org/pdf/0707.3953v3 because the named local PDF is absent.
This confirms the normal Noetherian model and geometric-reducedness clauses;
§1.2 confirms the schematic-density convention for modifications. No correction
or STATEMENT-DISPUTED issue was found.

Edge cases checked: S is nonempty by integrality. Z and Z' may be empty; sectionwise
injectivity and the whole empty isomorphism open still make sense. A field base,
the identity modification, empty fibres, arbitrary characteristic, nonseparated
families, and non-Noetherian normal bases are admitted. There is no finite-presentation
hypothesis on f, no flatness hypothesis on q, and no properness hypothesis on p.
All schemes use the same arbitrary universe u, consistently with the dependency APIs;
no test-field universe below the base's universe is introduced.

Searches (all run for this item with msearch.py):

- LeanFinder: `Noetherian approximation of a finite modification over a normal integral
  affine base with flat finitely presented geometrically reduced fibres`: eight hits,
  about locally Noetherian schemes and finite type, no exact approximation theorem.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsIntegral`: zero hits.
- Mathlib grep: `EtaModification|etaModification|SchematicallyDense|normal.*approximation`
  in AlgebraicGeometry: zero hits.
- LeanSearch: `Noetherian approximation of finite generic modifications of flat finitely
  presented geometrically reduced schemes`: eight Noetherian / flatness hits, no match.
- Direct rg on the upstream WeilConjectures tree for the item id: no result. Direct rg
  on upstream and lean/Sheaf for normal approximation found the existing normal-family
  and normal-refinement statements, none descending this finite modification.
- Direct rg on upstream and lean/Sheaf for eta-modification and schematic density found
  the curve-and-marking-specific `MultipointedCurve.Hom.IsEtaModification`, whose
  source/target type does not apply here. Its sectionwise density and canonical
  base-change map definitions were read as conventions, not copied as a new definition.
- Full-name check in dag/lean_names_upstream.json, upstream WeilConjectures, Mathlib,
  and lean/Sheaf: no existing declaration with the new theorem name.

Validation: scompile.py compiled the sandbox module and its library path independently,
with no errors or warnings (8.4 s and 4.8 s on the first run). Every binder and universe
is explicit and `autoImplicit` is disabled. All lines are at most 100 characters.

## Second reading by Q44

Local clause-by-clause rereading of the node and completed Lean file: the input and model
both retain properness, finiteness, generic-fibre isomorphism and schematic density in
both source and target; finite presentation has all three factors on each side.
The model generic point is introduced explicitly so no existential typeclass instance
or `letI` is hidden in the conclusion. Both scheme isomorphisms are present and their
commutative square implies source as well as target compatibility over S. The integral
input supplies the domain-stalk part of normality; it is included explicitly for the
existential base, whose integral conjunct is not a local instance. No mismatch was found.
This is a local rereading, not a claim of review by another agent: the dispatcher brief
forbids starting another agent and assigns independent review to the maintainer.
