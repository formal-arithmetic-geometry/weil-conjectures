## Worker report

The module `Sheaf.Paper.RootTowerLisseMorphismExtension` states
`AlgebraicGeometry.ProEtale.rootTower_lisse_restriction_bijective`; its only postponed
proof is this theorem. Three helpers contain real data: `parameterRootOpen`,
`parameterRootProjection`, and `rootTowerRestrictionComparison`. There are no new nodes,
dependency repairs, or statement corrections. The source paragraph is the current
main-20261015 direct-images proof, paragraph (3); the node explicitly identifies this
particular expanded morphism-extension input as agent formulated and its exact
all-continuous literature reference as wanted. This delivery does not claim to resolve
that outstanding reference obligation.

Hypotheses and clauses:

- The distinct primes are `p ℓ`, their `Fact _.Prime` instances and `hpℓ : p ≠ ℓ`.
  The field is `k : Type u`, `[Field k] [CharP k p]`. The finite norm-topological
  extension is `E : Type u`, `[NormedField E] [NormedAlgebra ℚ_[ℓ] E]` and
  `[FiniteDimensional ℚ_[ℓ] E]`; the normed algebra structure fixes the norm topology.
- All coefficients are `Profinite.continuousCoefficientRingObj E`: sections are the
  actual lifted continuous maps `C(P,E)`, with pointwise operations and precomposition.
  This is definitionally the `continuousMapRingObjOfUniverse` dependency's underlying
  sheaf when both universes are u; theorem proofs in the sheaf structure are irrelevant.
  `ContinuousCoefficientCommRing` exports its pointwise commutative ring-object
  structure for the existing module framework. No discrete replacement is used.
- `Y`, `y : Y ⟶ Spec k`, `[LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]`
  render separated finite type; `hY : IsRegularScheme Y` includes local Noetherianity
  and stalkwise regularity. `b : Spec A ⟶ Y`, `[Etale b]`, is the affine etale chart.
- `r` and `t : Fin r → A` give all parameters, including the empty list. `H` is the
  closed divisor ideal; `hH : IsStrictNormalCrossingsBoundary H` includes effective
  Cartier, radical, and the regular-intersection conditions. `hproduct` identifies
  the ideal itself with the principal ideal of the product, transported through
  `ΓSpecIso.inv`, not merely equality of zero sets. `hbranches` says the set of the
  `V(t_i)` is exactly the images in Spec A of the irreducible components of the
  support subtype. Together with reducedness of the product divisor, the parameter
  branches have multiplicity one.
- `R`, `a : A →+* R`, and `[WeaklyEtale (Spec.map ... a)]` give the affine small
  pro-etale object U, using the project's weakly-etale small-site convention.
- The tower is the actual `Spec (tameRootAlgebra p (fun i ↦ a (t i)))`.
  `TameRootOrder` is the positive integers prime to p; `tameRootRelations` imposes
  `x_(i,n)^n = t_i` and `x_(i,m)^(m/n) = x_(i,n)` for n dividing m. This simultaneous
  generators-and-relations presentation is exactly the displayed filtered colimit:
  each finite root stage maps into it, compatibly, and a compatible family of stage
  maps factors uniquely through its quotient. Reuse of this existing presentation
  adds the landed `def-sfb-strict-local-kummer-tame-module` to statement dependencies.
- `parameterRootOpen` is the basic open of the image of the parameter product, hence
  exactly the base change of B[1/product] to T. Its `.ι` is the open inclusion j.
- `N N'` are internal modules `CategoryTheory.Mod` over `condensedRingObj C_E T` in
  `Sheaf (Scheme.ProEt.topology T) Ab`. `hN hN' : IsLisseCoefficientModule ...`
  use the recorded pro-etale locally finite free predicate, with varying finite ranks.
- The first `Function.Bijective` applies to the actual functorial map
  `(CondensedRing.upperStar C_E j).map` on Hom(N,N'). This is full faithfulness
  between supplied modules; it makes no object-extension or essential-surjectivity claim.
- For every scheme `U'`, `v : U' ⟶ Spec R` and `[WeaklyEtale v]`, the first projection
  `g : T ×_U U' ⟶ T` is written using `pullback.fst`. The second Hom bijection is
  restriction along `pullback.fst g j` on `g* N, g* N'`. It also covers nonaffine U'.
  The last equality, for every `f : N ⟶ N'`, is exactly commutation with pullback
  after the canonical comparison `j'^* g^* ≅ g°^* j^*`. The helper constructs this
  comparison solely from `CondensedRing.upperStarComp` and `pullback.condition`.
  The two bijections and this square also give commutation of their inverses: by
  uniqueness, pulling back an extension extends the pulled-back morphism.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingSheafOfUniverse`
  and its underlying abelian ring-object construction. Its section formula was read
  alongside `ContinuousCoefficientUniverse` and `ContinuousCoefficientCommRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj` and its commutativity instance; `UpperLowerStar.Defs` supplies
  `CondensedRing.upperStar` and `upperStarComp`, including coefficient transport.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, action axioms,
  action-compatible morphisms and regular module.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, whose objects are
  weakly-etale maps, and `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`;
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFree` and `finiteFree`.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `TameRootOrder`, `tameRootRelations`,
  `tameRootAlgebra`, read in full and reused without a duplicate construction.

The module also imports all recorded, stated proof-dependency modules, non-publicly:
normal ring integrality, Spec idempotents/clopens, affine qcqs and spectral topology,
component homeomorphism, continuous realization and Cartesian coefficients. The unstated
`lem-sfb-snc-root-limit-normal-charts` has no module to import; its precise role and all
other eight proof steps are retained in the theorem docstring. It is a proof input,
not a missing notion needed to type this statement.

Edge cases checked: r=0 gives a polynomial quotient on an empty variable set and product
1, so the open is the entire tower; ranks zero are admitted by `Mod.IsFree` (finiteFree
rank zero), with empty Hom matrices; the zero ring and empty chart are allowed (no
nontriviality or inhabitedness binder); varying ranks on disconnected charts are allowed;
base change includes the identity, empty source, and arbitrary nonaffine weakly-etale
sources. Both scheme and coefficient universes are explicitly bound at u, with site
objects at u+1 and morphisms at u; no equality of those universes is imposed.

Searches actually run:

- msearch leanfinder: “Restriction of lisse continuous coefficient modules from a normal
  infinite root tower to its open complement is fully faithful”: eight hits, including
  `LightCondMod.LocallyConstant.fullyFaithfulFunctor`, the corresponding condensed
  discrete results and `Scheme.Modules.fullyFaithfulToPresheafOfModules`; none states
  this root-tower restriction assertion.
- msearch leansearch: “Morphisms of lisse pro etale modules over continuous p adic
  coefficients extend uniquely from the punctured parameter root tower”: eight hits
  about p-adic functions/characters, condensed Kan extensions and formal unramifiedness;
  no match.
- msearch loogle: `CategoryTheory.Functor.map, Function.Bijective`: generic Hom-map
  bijectivity and full-faithfulness criteria, including
  `FullyFaithful.nonempty_iff_map_bijective`; no geometric extension assertion.
- msearch grep: `(lisse|localSystem).*(fullyFaithful|dense)|(fullyFaithful|dense).*(lisse|localSystem)`:
  zero Mathlib hits. A separate rootTower/RootTower/rootLimit/RootLimit wrapper query
  returned zero hits; the supplied subdirectory was not used as absence evidence.
- rg over `lean/Sheaf` and `lean/WeilConjectures` for rootTower, RootTower, rootLimit,
  RootLimit, parameterRoot, ParameterRoot and Kummer found the existing strict-local
  tame algebra (reused), one-prime Kummer towers, and unrelated number-field roots.
  Searching the item id and candidate theorem name returned no declaration. DAG
  root/Kummer search located `def-sfb-strict-local-kummer-tame-module`.

Validation: scompile.py successfully compiled both the sandbox name and final module
name without errors or warnings (7.5s and 7.2s before the final explicit-import additions).
The initial failures were repaired: the scheme finite-type convention uses
LocallyOfFiniteType plus QuasiCompact; the coefficient construction now uses the
already-exported commutative universe-compatible interface, avoiding slow transport
between the separate tensor-structure encodings. No timeout limit was increased.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
