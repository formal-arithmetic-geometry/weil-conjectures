## Worker report

Item: lem-weil-pbc-symmetric-images-module-colimit. The new module
`Sheaf.AlgebraicGeometry.SymmetricImagesModuleColimit` states
`AlgebraicGeometry.Scheme.CommAlgebraSheaf.symmetricImagesModuleColimit`.
Its sole theorem has proof `sorry`; no construction or proof is added. The node is
unchanged except for `lean`, whose signature is copied verbatim from the source.
No new nodes, dependency repairs, or statement corrections are needed.

The source was read in `literature/stacks-project/properties.tex`: the proof of
lemma-algebra-directed-colimit-finite-presentation (Tag 05JS), beginning with the
module colimit and symmetric algebras, and the image argument in the proof of
lemma-algebra-directed-colimit-finite-type (Tag 05JT). The qcqs assumption in those
lemmas is needed to obtain the presentations in the first place. This item is
conditional on a supplied presentation and adds no qcqs hypothesis.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- A scheme is `X : Scheme.{u}`. The algebra sheaf is
  `A : X.CommAlgebraSheaf`, the existing under-category of the structure ring
  sheaf. `hA : A.toModule.IsQuasicoherent` is precisely quasi-coherence of its
  underlying module.
- The index is `I : Type v` with `[Preorder I]`,
  `[IsDirected I (· ≤ ·)]`, and `[Nonempty I]`. The independent universe `v` permits arbitrary index sets without imposing
  a size relation to the scheme; preorders need not be partial orders.
- The system and its linear transition maps are `F : I ⥤ X.Modules`.
  `hF : ∀ i, (F.obj i).IsFinitePresentation` is Mathlib's local finite
  presentation by finite free sheaves, as the dependency's clause (0) uses.
  It does not impose global finite presentation of the module of sections on
  an arbitrary nonaffine open.
- `φ : F ⟶ (Functor.const I).obj A.toModule` records the given module maps
  and their compatibility with the transition maps. The hypothesis
  `hc : IsColimit (Cocone.mk A.toModule φ)` states the colimit in the full
  category of structure-sheaf modules with exactly these maps and target.
  No chosen colimit object or unrelated isomorphism replaces the supplied maps.
- The first conjunct `∀ i, (F.obj i).IsQuasicoherent` gives the claimed
  quasi-coherence of all the finitely presented stages.
- `ψ : ∀ i, SymmetricAlgebraSheaf.algebra (F.obj i) ⟶ A` uses the dependency's
  explicit sheafification construction. Its degree-one map is
  `SymmetricAlgebraSheaf.inclusion (F.obj i)`. For every open and every module
  section the first conjunct says `ψ_i(j_i(x)) = φ_i(x)`. The following
  universally quantified `t` clause states uniqueness among all algebra maps
  satisfying that identity, on all opens.
- `C : I → A.finiteTypeQuasiCoherentSubalgebras` uses exactly the recorded
  subtype of algebra-sheaf subobjects with quasi-coherent underlying modules
  and finite type on every affine open. Inclusions are `(C i).val.arrow`.
  Thus no independent copy of the finite-type subalgebra notion is defined.
- The clause over all opens `U` and algebra sections `s` identifies membership
  in the inclusion's range with local membership in `ψ_i`'s range: for every
  point `p ∈ U` there is an open `V ≤ U` containing `p` whose restriction of
  `s` lies in `Set.range ((ψ i).right.hom.app (op V))`. This specifies the
  actual sheaf image, not just an arbitrary containing subalgebra. The
  subobject encoding already gives an inclusion; it does not assume a
  sectionwise-image description on arbitrary opens.
- Under `IsAffineOpen U`, equality of the two section-map ranges expresses
  `C_i(U) = ψ_i(Sym(F_i)(U))`, inside `A(U)`.
- The next affine conjunct is
  `Module.FinitePresentation Γ(X, U) Γ(F.obj i, U)`.
- For every `n : ℕ` and `f : Fin n → Γ(F.obj i, U)`, the hypothesis
  `Submodule.span Γ(X, U) (Set.range f) = ⊤` expresses the finite module
  generating list. The conclusion says that `Algebra.adjoin` of its images
  under `φ_i,U`, as a subset of `A(U)`, equals the inclusion's range. This is
  exactly algebra generation of `C_i(U)`. The scalar algebra structure in
  `@Algebra.adjoin` is explicitly `(A.hom.hom.app (op U)).hom.toAlgebra`,
  so it is the prescribed structure map. No extra algebra structure is bound,
  and no hidden `let` in the statement prevents downstream reduction.
- Finally every affine open and every `a : A(U)` have witnesses `i` and
  `x : Γ(F.obj i, U)`. The final three conjuncts assert
  `a = φ_i,U(x)`, `a = ψ_i,U(j_i,U(x))`, and membership in `C_i(U)`.
  These refer to the same extension and image family as all earlier clauses.

Dependency declarations and imports, checked against their recorded source files:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  available through the public imports. These provide the scheme, its opens,
  and the structure sheaf.
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`:
  `AlgebraicGeometry.Scheme.CommAlgebraSheaf` and `.toModule`;
  available through both algebra-sheaf statement dependencies.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` is the conjunction
  of existing `SheafOfModules.IsQuasicoherent` and `.IsFiniteType`.
  This theorem only needs quasi-coherence, so it uses that underlying Mathlib
  predicate directly, not the stronger conjunction. The module is publicly
  imported as the node's recorded dependency.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` is a transparent abbreviation for
  `SheafOfModules`; `X.Modules` is the existing scheme specialization.
  This statement dependency is publicly imported, retaining the canonical
  module category and its morphisms.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `colimit`;
  the theorem uses the first two for the supplied colimit. Filtered/directed
  index structures come from `Mathlib.CategoryTheory.Filtered.Basic`.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `AlgebraicGeometry.SymmetricAlgebraSheaf.algebra`, `.inclusion` (and its
  sectionwise `.sectionMap` read in the construction); publicly imported.
- `Sheaf.AlgebraicGeometry.FiniteTypeQuasiCoherentSubalgebras`:
  `AlgebraicGeometry.Scheme.CommAlgebraSheaf.finiteTypeQuasiCoherentSubalgebras`;
  publicly imported and used directly for `C`.
- The sectionwise finite presentation predicate has the explicit public import
  `Mathlib.Algebra.Module.FinitePresentation`. The first compiler attempt
  diagnosed that this declaration was otherwise only privately imported;
  making its defining module public repaired the module-mode visibility.
- Proof-only imports preserve all stated proof dependencies:
  `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
  (`AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`);
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`
  (`AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra_core`);
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`
  (`AlgebraicGeometry.quasiCoherentSymmetricAlgebra_affine_comparison`);
  `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal`
  (`AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernel_image_quasiCoherent`);
  `WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation`
  (`SymmetricAlgebra.generators_and_finitePresentation`);
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
  (`AlgebraicGeometry.Scheme.Modules.quasiCoherentModuleColimitAffineSections`).
  The symmetric-algebra construction and finite-type subalgebra modules are
  already public imports because they are also statement dependencies.

Edge cases checked mathematically before finalizing the statement:

- Empty scheme and empty affine open: all pointwise locality conditions are
  vacuous where appropriate, and the zero section is represented because `I`
  is nonempty. No nonempty scheme hypothesis is imposed.
- Zero stage modules and `n = 0`: the empty module generating list is allowed.
  Its symmetric-algebra image is the scalar subalgebra, and the adjoin of the
  empty set is exactly that scalar subalgebra, as required.
- Zero target algebra and noninjective structure maps, stage maps or extension
  maps: only the image inclusion is a subobject; none of those other maps is
  required to be injective or surjective.
- Singleton directed index: the colimit condition gives the expected result
  with that stage. Nonantisymmetric preorders are also allowed.
- Non-Noetherian rings and non-qcqs schemes: the proof uses finite presentation
  locally and affine quasi-coherent exactness; there is no omitted global
  finiteness assumption once the module system is supplied.
- Sheaf image on nonaffine opens is defined by local lifting. Equality with a
  sectionwise range is claimed only for affine opens, as in the node.

Searches for an exact existing theorem (all through the prescribed msearch wrapper):

1. LeanFinder query: `A directed colimit of finitely presented module sheaves gives
   symmetric algebra images which are finite type quasi coherent and cover affine sections`.
   Eight hits, all module finite-presentation/quasi-coherence APIs, including
   `SheafOfModules.IsFinitePresentation.exists_quasicoherentData`,
   `SheafOfModules.quasicoherentDataOfIsFinitePresentation`, and
   `SheafOfModules.Presentation.isColimit`. None states the algebra image theorem.
2. Loogle query: `SymmetricAlgebra, Algebra.FiniteType`. Zero hits.
3. Mathlib grep query:
   `(SymmetricAlgebra|symmetricAlgebra).*(sheaf|[Ii]mage)|[Ii]mage.*(SymmetricAlgebra|symmetricAlgebra)`.
   Zero hits.
4. LeanSearch query: `Images of symmetric algebras of finitely presented module sheaves
   are finite type quasi coherent subalgebras and cover affine sections of their directed
   module colimit`. Eight hits, including `SymmetricAlgebra`, finite presentation
   instances, and `SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`.
   None gives the image-and-coverage assertion.
5. `rg -n 'symmetric.images|symmetricImages|lem-weil-pbc-symmetric-images-module-colimit'`
   in both `lean/WeilConjectures` and `lean/Sheaf`: no match. A further exact
   declaration-name search in both roots and `dag/lean_names_upstream.json`
   gave no match. Searches for `Algebra.adjoin`, `toAlgebra`,
   `finiteTypeQuasiCoherentSubalgebras` and `Subobject.mk` found the dependency
   interfaces and ring-level ingredients used above, not an exact theorem.

Validation: the delivered file begins with the required module header, exposes
its declarations publicly, sets `autoImplicit false`, and has no lines over 100
characters. `scompile.py Q74 lem-weil-pbc-symmetric-images-module-colimit <file>`
passed in both sandbox mode (8.9 seconds) and named library mode (9.3 seconds)
without errors or warnings. No local Lean invocation or global build was used.
The full proof plan from the node appears in the theorem docstring.

No STATEMENT-DISPUTED flag or node fault remains. The maintainer supplies the
independent review; no second reader was spawned or represented as having read
this delivery.

Resume validation: the initial resumed dry run passed at commit `07f6a52b6bd`.
The index universe was then made independent (`universe u v`, `I : Type v`)
to avoid an unnecessary size restriction; the final dry run validates this version.
The revised file passed `scompile.py` in sandbox mode (20.0 seconds) and
named library mode (10.4 seconds), with no errors or warnings.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
