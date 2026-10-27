## Worker report

The module `Sheaf.AlgebraicGeometry.ProperDualizingClosedStalkNormalized` states
`AlgebraicGeometry.proper_dualizing_closed_stalk_normalized`. Its only theorem has
proof `sorry`. The two helper definitions contain actual constructions, with no
postponed data or arbitrary maps. The accepted stage-1 split and natural-language
statement are unchanged; the node copy adds only `lean`.

The inherited stage-1 BLOCKED ending is superseded by the explicit stage handoff
in coord/brief-stage2.md section 0. The current queue lists this node in stage 2,
and the node has no Lean record and no released repair note. This delivery records
its statement; it does not reopen or re-split the accepted proof.

Source read: Stacks duality.tex, Tag 0AWL, lemma-good-dualizing-normalized,
including its proof, and Tag 0AWI, example-proper-over-local. Over Spec(k), the
base dualizing complex is k[0]. The finite residue-field dual is one-dimensional
over that residue field even for inseparable extensions, giving the stated
isomorphism, without choosing a canonical identification with the residue field.
The item is a supporting node, not a blueprint unit's own statement.

Hypotheses and clauses, in the order of the node:

- A field k: `(k : Type u) [Field k]`.
- A scheme X and proper structure map to Spec(k): `(X : Scheme.{u})`,
  `(f : X ⟶ Spec (.of k)) [IsProper f]`.
- The supplied right adjoint a: the functor binder has source
  `DerivedCategory (ModuleCat.{u} k)` and target `schemeDerivedQCohCategory X`;
  `_adj : properFieldDerivedDirectImage k X f ⊣ a` specifies its adjunction to
  the actual direct image, not to an arbitrary functor.
- The helper `properFieldDerivedDirectImage` composes the existing QCoh inclusion,
  `schemeDerivedDirectImage f`, and right-derived global sections on Spec(k).
  The last functor restricts scalars through `(Scheme.ΓSpecIso (.of k)).inv.hom`.
  This is exactly the inverse affine identification in
  `exists_affineQCohDerivedEquivalence`, not an added mathematical hypothesis.
- K = a(k[0]): every occurrence is `a.obj` applied to
  `(DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)`;
  `.obj` forgets the full QCoh subcategory. There are no hidden let binders.
- Every closed point: `(x : X) (_hx : IsClosed ({x} : Set X))`.
- A = O_{X,x}: the actual ring `X.presheaf.stalk x` throughout.
- Residue field A/m_x: `X.residueField x`, with its A-module structure supplied
  by `ModuleCat.restrictScalars (X.residue x).hom`. It is not treated as an
  arbitrary module or assumed equal to k.
- A is Noetherian: the first conjunct `IsNoetherianRing (X.presheaf.stalk x)`.
- K_x has a bounded injective representative: the second conjunct quantifies
  `I : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ`, lower and upper
  integer bounds outside which `IsZero (I.X n)`, degreewise `Injective (I.X n)`,
  and `Nonempty (DerivedCategory.Q.obj I ≅ properDualizingStalk ... K)`.
- Every H^j(K_x) is finitely generated: the third conjunct is `∀ j : ℤ`,
  `Module.Finite` of `DerivedCategory.homologyFunctor ... j` of that same stalk.
- The scalar-action map is an isomorphism: the fourth conjunct is
  `IsIso (MonoidalClosed.curry' (𝟙 K_x))`. Mathlib's curry' transposes a morphism
  X → Y to the morphism from the tensor unit to internal Hom(X,Y). Here it
  transposes the identity, hence is precisely homothety. The derived module
  tensor unit is A[0], and `ordinaryModuleDerivedInternalHom` is definitionally
  the same closed internal-Hom bifunctor, with K-injective construction.
- Normalization: the final conjunct is `Nonempty` of an isomorphism in D(A)
  from `ordinaryModuleDerivedInternalHom` applied to the degree-zero residue
  module and K_x to the degree-zero residue module. The isomorphism is in the
  derived category itself, not merely separately in every cohomology degree.
- The exact stalk construction is `properDualizingStalk`: apply the recorded
  `RingedSpace.moduleStalkFunctor` termwise to `DerivedCategory.Q.objPreimage K`
  and localize. Stalk exactness ensures that every representative gives an
  isomorphic result. This adds no arbitrary comparison or theorem assumption.
- No dimension, reducedness, connectedness, smoothness, or rationality assumption
  appears. Independent `wX` and `wS` localization universes are explicitly bound;
  module derived categories use the published standard construction. Their
  `HasDerivedCategory` binders are the project's required localization data,
  not finiteness hypotheses. `set_option autoImplicit false` checks all binders.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field, a Mathlib leaf).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage:
  `schemeDerivedDirectImage`.
- WeilConjectures.Topology.PresheafModuleStalkFunctor:
  `PresheafOfModules.moduleStalkFunctor`; on sheaves the node's own record directs
  consumers to `RingedSpace.moduleStalkFunctor`, from
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor. The latter uses exactly
  the same stalk carriers and linear action.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Scheme.residue`.
- Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, abbreviation for the
  existing derived closed Hom, preserving the generic ringed-site definition.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic: `CategoryTheory.Injective`;
  the node's other declaration `InjectiveResolution` was also read, but the
  conclusion needs an arbitrary bounded integer-indexed injective complex.
- Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`.

Plain proof imports preserve every available recorded proof dependency:
`ModuleStalkExact`, `CoherentFiniteType`, `ClosedPointField`,
`NoetherianDerivedDirectImageRightAdjoint`, `FiniteFlatDualityEvaluation`,
`AffineQCohDerivedEquivalence`, `ProperUpperShriekComposition`,
`FinitePushforwardCoherent`, `FiniteDualityDerivedHom`. Mathlib proof leaves
use Noetherian, ClosedImmersion, Finite and Flat; proper composition and the
closed-immersion-to-proper instances are available in Proper and Finite.
`lem-sfb-proper-field-algebraic-dualizing` and
`lem-sfb-coherent-bounded-below-rhom-stalk` have no recorded modules yet, so
cannot be imported. They are proof prerequisites only; neither is needed to
write the present statement. No import cycle was introduced.

Searches for an existing statement:

- msearch leanfinder, "For a proper scheme over a field the dualizing complex
  has normalized dualizing stalks at every closed point": eight hits about
  stalk domains, residue fields and local stalk maps; none states normalization.
- msearch loogle, `"dualizing", "stalk"`: zero hits.
- msearch grep, `dualizing|dualising|normalizedDualizing`: fourteen matches,
  all comments about categorical dualization or unrelated uses.
- msearch leansearch, "The dualizing complex of a proper scheme over a field
  is normalized at each closed point": eight hits about scheme normalization,
  none about dualizing complexes.
- rg over WeilConjectures and Sheaf for the proposed names and
  `dualizing.*[Ss]talk|[Ss]talk.*[Dd]ualizing`: no matching coherent-duality
  statement; the matches concern etale smooth duality. grep of the item id
  over WeilConjectures gives no match.
- Search for existing derived stalk and affine derived global-section helpers
  found `SingleComplexBaseChange.comparisonDerivedStalk` and
  `affineDerivedGlobalSections`. Their interfaces fix a standard source
  localization or require family-wide derived-category instances. A module-mode
  compiler check confirmed that comparisonDerivedStalk cannot accept the
  present K in its arbitrary supplied localization. The helper here directly
  implements the representative construction the node expressly specifies,
  using the existing stalk functor; no equality of universes or second module
  category is imposed. The affine coefficient-transport expression also agrees
  with the published inverse in exists_affineQCohDerivedEquivalence.

Edge cases checked: X empty makes the closed-point assertion vacuous. For
X = Spec(k), K = k[0] gives the field's usual self-duality. For a finite
non-rational or inseparable extension L/k, Hom_k(L,k) is still rank one over L;
there is no trace/separability assumption. Zero terms and zero cohomology satisfy
injectivity and finite generation. The integers p,q are unrestricted, so no
unjustified degree or dimension bound is imposed; a zero complex is allowed.
The theorem covers disconnected, nonreduced, singular, and higher-dimensional
proper schemes. Closedness is essential and is explicitly retained.

No statement correction, disputed statement, new DAG node, or dependency-record
repair was required. Each declaration has a source and blueprint docstring;
the theorem docstring contains all six accepted proof steps. Initial and final
versions compile with scompile.py, with no errors or non-sorry warnings. The
intermediate attempt to reuse the incompatible derived-stalk interface was
removed before delivery. Independent statement review is the maintainer's.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
