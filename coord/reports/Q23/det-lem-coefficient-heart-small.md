## Worker report

The module `Sheaf.Paper.CoefficientHeartSmall` states
`AlgebraicGeometry.ProEtale.coefficientHeart_essentiallySmall`, with its sole proof
`sorry`. It introduces no definitions. The node changes only in `lean`; there are
no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The algebraic closure is the existing `PadicAlgCl ℓ` of `ℚ_[ℓ]`.
- A finite subextension is `E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)` with
  `FiniteDimensional ℚ_[ℓ] E`. This specifies the embedding and scalar compatibility,
  rather than an unrelated field or a finitely generated extension.
- `Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}` is the condensed
  coefficient ring. `hΛ` is exactly the alternative that Λ is
  `Profinite.padicSubfieldCondensedRing ℓ E` for such an E, or is
  `Profinite.padicAlgClCondensedRing ℓ`. The former uses the restricted valuation
  topology; the latter consists of continuous maps valued in a finite subextension,
  not all continuous maps into the algebraic closure.
- `sheafCompose ... (forget₂ RingCat Ab)` takes the underlying abelian ring object
  with its existing canonical multiplication and unit. Its `IsCommMonObj` binder
  records commutativity needed by the existing constructibility interface. Both
  allowed coefficients supply this structure; this adds no condition on E, ℓ or X.
- `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]` renders exactly the
  node's meaning of Noetherian: locally Noetherian and quasi-compact. No separatedness,
  dimension, base field, connectedness, or nonemptiness assumption is added.
- `ConstantModelConstructible ... X` is the recorded full subcategory Cons from
  `sk-def-sfb-constructible`. Its objects use `IsConstantModelConstructible`, finite
  constant scalar models on a finite constructible stratification in the qcqs case.
  Local Noetherianity supplies quasi-separatedness, so the qcqs branch applies here.
  Its ambient module ring is the existing `condensedRingObj Λ X = p_X^* Λ`.
  There is no replacement by a discrete constant ring or arbitrary local matrices.
- `EssentiallySmall.{u + 1}` asserts smallness in the specified larger universe.
  The site consists of schemes in bound `u`, with objects in `u + 1` and morphisms
  in `u`; coefficient sections are in `u + 1`. The ambient module category may
  have objects in `u + 2`. Thus the conclusion is a genuine smaller set of
  representatives, not smallness in the ambient category's object universe.
  Mathlib's `essentiallySmall_iff` identifies this with smallness of its skeleton
  (the isomorphism classes) together with local smallness. The latter follows
  independently from natural transformations on this bounded site; it is not an
  extra mathematical conclusion or hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`, the already recorded weakly-etale site.
- `def-weil-size-convention` has no Lean object by its recorded metatheoretic
  convention. Explicit `universe u`, the site sizes, and `EssentiallySmall.{u + 1}`
  implement it.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`, with no Hausdorff requirement.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicSubfieldCondensedRing`, `Profinite.padicAlgClCondensedRing`, and
  `Profinite.padicAlgClRingObj`. The first two dependency nodes have no `lean`
  record but their closed slopmaster2 audits explicitly name these declarations;
  they are used directly, without restating them.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, and
  `condensedRingObj`, transporting the coefficient ring along `upperStarFromPoint`.
  These are the published framework declarations in the side overlay; the older
  source checkout is not used as a substitute. Read `coord/pefw-upstream-framework.md`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `ConstantModelConstructible` (with `HasFiniteConstantLocalModel` and
  `IsFiniteConstantStratified` read in full). Its current server source was also
  confirmed with `scompile.py --source`.
- `Mathlib.CategoryTheory.EssentiallySmall`: `CategoryTheory.EssentiallySmall`
  and `essentiallySmall_iff`, for the conclusion.

The module's nonpublic imports retain the recorded proof plan: internal/sectionwise
module equivalence, ringed-site modules, sheaf tensor, finite locally closed
stratifications, finite presentations, vector-space bases, sheafification, free
scalar extension, common stratifications, weakly-etale localization, inverse image,
site-covering axioms, and the condensed module adjunction framework. Closed
upstream proof dependencies use their audited modules. Mathlib Noetherian and the
public constructibility imports also expose the cartesian-coefficient and module
pullback declarations. The theorem docstring spells out all nine current DAG
steps, including the explicit equalizer descent models and the embedding in the
finite product of stratum direct images, followed by the bound on subsheaves.

Edge cases checked before writing: empty X (only the zero sheaf), empty strata,
rank-zero scalar modules, distinct ranks on empty overlaps, E equal to the base
field, every prime including 2, either coefficient alternative, and nonseparated
Noetherian X. Nothing in the signature excludes these cases. The descent code
argument does not require a finite trivializing cover or identity transition
matrices on the whole self-overlap; it uses only diagonal normalization.

Searches made, before writing:

- `msearch.py leansearch`, query `constructible l-adic sheaves are essentially small`:
  eight generic size/sheaf results, including `EssentiallySmall` and small-site
  infrastructure, no statement for this constructible coefficient category.
- `msearch.py leanfinder`, query `The category of constructible sheaves with condensed
  l-adic coefficients on a Noetherian scheme is essentially small`: eight results
  on LightProfinite, LightCondensed and generic Grothendieck abelian categories;
  no exact theorem.
- `msearch.py loogle`, query `CategoryTheory.EssentiallySmall,
  CategoryTheory.ObjectProperty.FullSubcategory`: six generic full-subcategory
  smallness/closure results; none asserts the needed constructible smallness.
- `msearch.py grep`, query `EssentiallySmall|Skeleton` in
  `CategoryTheory/EssentiallySmall.lean`: five hits giving the size definitions.
  Read the complete signature, docstring and skeleton characterization.
- `rg` of the upstream WeilConjectures tree, shared `lean/Sheaf`, published framework,
  and `dag/lean_names_upstream.json`, for the item id, `coefficientHeart.*[Ss]mall`,
  and constructible/essentially-small combinations: no existing theorem for
  finite-constant-model condensed coefficients. The private theorem
  `constructible_essentiallySmall` in `ConstructibleFilteredData.lean` concerns
  finite discrete etale coefficients, so it is a different category and coefficient.
  Existing `CondensedConstantConstructibility` and the coefficient constructions
  were found and reused. No duplicate definition was introduced.

The maintenance note for this item is a resolved stage-1 re-splitting note dated
2026-10-17. The current nine-step DAG plan was retained without alteration.
No node fault or STATEMENT-DISPUTED issue was found.

Validation: the delivered module compiled through the prescribed `scompile.py`
wrapper without errors or warnings, under the standard 60-second per-file limit.

Additional scratch consumer validation (not delivered): instantiated the theorem
for an arbitrary finite intermediate field with `FiniteDimensional`, obtaining
commutativity from its canonical restricted normed-field structure, and for the
algebraic-closure coefficient. Also synthesized `LocallySmall.{u + 1}` for the
full constructible category with an arbitrary commutative condensed ring, without
using the theorem or its coefficient alternative. All three consumers compiled
cleanly through `scompile.py`, confirming the claimed interfaces and the skeleton
interpretation. The delivery dry run passed compilation and server preflight.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
