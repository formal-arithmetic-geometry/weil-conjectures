## Worker report

The module `Sheaf.AlgebraicGeometry.RegularSurfaceBirationalRationalLocalRings`
states `AlgebraicGeometry.subsingleton_H_one_of_regular_surface_birational_local_extension`.
Its sole proof is `sorry`. No definition, additional theorem, or corrected natural-language
statement is introduced. The mathematical source was read directly in
`literature/stacks-project/resolve.tex`: `definition-reduce-to-rational` (0B4N),
`lemma-regular-rational` (0B4Q), `lemma-rational-propagates` (0BG0), and the normal
modification convention preceding `situation-vanishing`.

Hypothesis and conclusion correspondence:

- The commutative ring `R` is `(R : Type u) [CommRing R]`.
- Regular locality is `[IsRegularLocalRing R]`. This class includes locality and
  Noetherianity, with the maximal ideal's generator count equal to `ringKrullDim R`.
- The domain hypothesis is the explicit proposition `(hRdomain : IsDomain R)`.
  Making it an ordinary proof argument avoids the overlapping-instance warning for
  `Nontrivial R` inherited from both the domain and regular-local structures. It is still
  precisely the domain hypothesis and can be registered as an instance in the later proof.
- Excellence is `(hR : IsExcellent R)`, using the dependency's actual definition.
- Dimension two is `(hdimR : ringKrullDim R = 2)`.
- The second commutative local domain is `(B : Type u) [CommRing B] [IsDomain B]
  [IsLocalRing B]`. Its normality is `[IsIntegrallyClosed B]`, the recorded normal-domain
  convention together with `IsDomain B`. Its dimension is `hdimB : ringKrullDim B = 2`.
- The injective local inclusion is `(i : R →+* B) [IsLocalHom i]
  (hi : Function.Injective i)`. It does not impose that the two ring carriers are literal
  subsets; it records exactly the stated injective local homomorphism.
- Equality of fraction fields under this inclusion is `hfrac : Function.Bijective
  (IsFractionRing.map (K := FractionRing R) (L := FractionRing B) hi)`.
  This is the canonical map induced by `i`, not the existence of an unrelated field
  isomorphism. Bijectivity is equivalent to its being an isomorphism of fields.
- Essential finite type is `hfinite : i.EssFiniteType`, Mathlib's existing ring-map
  predicate. Its algebra form is equivalent to existence of a finite type subalgebra and
  a submonoid whose localization is `B` (`Algebra.essFiniteType_iff_exists_subalgebra`).
  Thus this is precisely the node's parenthetical meaning, without extra finite
  generation of the localization itself.
- The arbitrary integral scheme is `(Z : Scheme.{u}) [IsIntegral Z]`.
- Its normality is `(hZ : IsNormalScheme Z)`. The existing definition includes
  integrality and integrally closed domain stalks. The integral instance also supplies
  the generic point; its repetition inside `hZ` is logically redundant, not stronger.
- The actual proper morphism is `(g : Z ⟶ Spec (.of B)) [IsProper g]`.
  `IsProper` is the recorded predicate; universal closedness supplies quasi-compactness,
  so its locally finite type clause agrees with finite type in the node.
- The assertion that `g` induces an isomorphism of function fields is expressed by
  `hgeneric : g (genericPoint Z) = genericPoint (Spec (.of B))` and
  `hbirational : Function.Bijective (g.stalkMap (genericPoint Z))`.
  By `Scheme.functionField`, function fields of integral schemes ARE the generic
  stalks. `hgeneric` identifies the source of this stalk map with the generic stalk
  of `Spec B`; its target is the generic stalk of `Z`. Consequently these hypotheses
  say exactly that the induced function-field map is an isomorphism. They do not
  replace the actual map by an arbitrary equivalence or assume an open isomorphism.
- The conclusion `H^1(Z, O_Z) = 0` is `Subsingleton (Sheaf.H' F 1 ⊤)`.
  Here `F` is `Z.sheaf` composed with
  `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat`.
  This is the additive structure sheaf on `Opens.grothendieckTopology Z`; the object
  `⊤ : Z.Opens` is the whole space. `Sheaf.H'` is the recorded ordinary sheaf
  cohomology declaration and `Subsingleton` is vanishing of its underlying group.
  It is not etale, pro-etale, or derived-category cohomology of another coefficient.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, with its `IsQuasiExcellent` and
  `IsUniversallyCatenary` constituents.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: its docstring and scheme predicate were
  read; the node's ring clause uses Mathlib `IsRegularLocalRing` from
  `Mathlib.RingTheory.RegularLocalRing.Defs`, as its record explicitly prescribes.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain` for the node's normal-domain clause.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType` underlie
  the existing `RingHom.EssFiniteType` in `Mathlib.RingTheory.EssentialFiniteness`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`; read its full
  signature and construction. Essential finite type uses Mathlib's existing ring
  localization interface, not a private reconstruction of module localization.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`, and
  `Scheme.Hom.stalkMap`.
- `Sheaf.AlgebraicGeometry.FunctionField`: read
  `Scheme.functionFieldOfComponents` and its docstring's arbitrary integral-scheme
  clause, which explicitly reuses Mathlib `Scheme.functionField` from
  `Mathlib.AlgebraicGeometry.FunctionField`. That is the generic stalk used here.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'`.
  The standard Grothendieck-abelian sheaf instances supply `HasExt`; no existence
  of cohomology or injectives is added as a theorem hypothesis.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`, the
  already recorded normal-integral-scheme predicate. The landed definition node
  `def-sbc-normal-dominant-galois` is added to `stmt_deps` to cite this existing notion,
  as authorized by brief-stage2 section 5. No record on that dependency is changed.
- Proof-only import `Sheaf.RingTheory.QuasiExcellentNagata` provides
  `isNagataRing_of_isQuasiExcellent`. The remaining proof-only dependencies
  `lem-per-regular-surface-rational`, `def-per-rational-surface-singularity`, and
  `lem-per-rational-singularity-birational-propagation` currently have no Lean record
  or Mathlib match; they therefore have no import yet. They are not needed to type
  the present statement. The docstring gives the node's full four-step proof plan.

Edge cases checked before writing:

- The empty scheme is excluded exactly by the node's integral hypothesis; no extra
  nonempty hypothesis is added. There is no generic point of the empty scheme to fake.
- Zero rings and fields are excluded by the domain and dimension-two hypotheses;
  a one-dimensional `B` is excluded explicitly, as the source requires.
- The identity extension `B = R`, `i = RingHom.id R` is allowed. The identity proper
  modification is allowed; it is consistent with affine higher-cohomology vanishing.
- Nontrivial proper birational modifications, including surface blowups and their
  normal modifications, are allowed; neither regularity of `Z` nor affine `Z` is assumed.
- A finite-degree non-birational proper map is excluded by bijectivity of its actual
  generic stalk map, even when its two function fields happen to be abstractly isomorphic.
- A non-surjective field embedding induced from `i` does not satisfy `hfrac`, even if
  some unrelated equivalence of the fraction fields exists.
- No characteristic, base field, algebraic closedness, residue-field equality,
  smoothness, projectivity, or regularity of `B` is imposed.
- The universe `u` is explicit and arbitrary. All ring carriers and schemes live in
  that ambient universe; there is no test family in a smaller independent universe.
- Cohomological degree is exactly one and the topology is exactly Zariski.

Searches made (all via the prescribed tools or read-only source searches):

- `msearch.py ... leanfinder` query: "A normal local surface domain birational and
  essentially of finite type over an excellent regular local ring has vanishing first
  structure sheaf cohomology on every normal modification". Eight hits: normalization
  preservation, smooth locus/cotangent support, and smooth charts. None states this result.
- `msearch.py ... loogle` query: `"rational", "singular"`. Zero hits.
- `msearch.py ... grep` query: `rational.{0,30}singular|birational.{0,30}cohomolog`.
  Zero hits.
- `msearch.py ... leansearch` query: "First Zariski structure sheaf cohomology vanishes
  on normal proper birational models of a normal local ring birational over an excellent
  regular surface ring". Eight hits on structure sheaves and generic stalk/localization
  constructions; no vanishing theorem or rational-singularity theorem.
- `rg` in the source `WeilConjectures` and the project's `lean/Sheaf`, for
  `rational.{0,30}singular|regular_surface|regularSurface|birational.*rational` and the
  exact item id: no duplicate theorem. One regular-surface principal-ideal theorem and
  birational common-dense-open source references are unrelated.
- Read-only searches for `IsNormal`, `IsNormalScheme`, birational maps, generic-stalk
  maps, `IsFractionRing.map`, `EssFiniteType`, `Sheaf.H'`, and structure-sheaf forgetful
  functors found the reused interfaces above. The existing `IsNormalScheme` was reused
  rather than copied. Mathlib `Scheme.Birational` is only an existence of a partial
  isomorphism of schemes and does not assert that the particular `g` induces it, so it
  was not substituted for the map-specific condition.

No statement dispute or source correction is needed. The sole node changes are `lean`
and addition of the existing normal-scheme dependency to `stmt_deps`.

Validation: the prescribed `scompile.py` checked both the sandbox and actual module name.
An initial error showed that `CommRingCat` has no direct `HasForget₂` to `AddCommGrpCat`;
using the two existing forgetful functors through `RingCat` fixed it. The instance
parameter adjustment above removed the overlapping-instance warning. The final line-wrap
fix addresses the only remaining style warning. Final clean compilation and server
preflight are run before delivery.

## Second reading by Q36

I reread the complete node and module after the first compilation. This is a single-worker
self-check; no independent worker was started under the dispatcher's explicit instruction.
The maintainer's independent delivery review remains separate.

The commutative excellent regular local domain and both dimension-two clauses occur as
`CommRing R`, `IsRegularLocalRing R`, `hRdomain`, `hR`, `hdimR`, and `hdimB`.
The normal local domain `B` occurs as `CommRing B`, `IsDomain B`, `IsLocalRing B`,
`IsIntegrallyClosed B`. The inclusion is the specified `i` with `IsLocalHom i`, `hi`,
`hfrac`, and `hfinite`; in particular, the fraction-field map uses this same `i`.
The universal normal modification is the arbitrary `Z`, `IsIntegral Z`, `hZ`, `g`,
`IsProper g`, `hgeneric`, and `hbirational`; the latter is the actual stalk map of `g`.
The conclusion is degree one at the terminal open of the Zariski site of `Z`, after
forgetting only the multiplication in its structure sheaf. Every node clause appears.
No regularity of `Z` or equality of residue fields was added. The ordinary domain proof
argument is still the original hypothesis, and duplicate integrality inside `hZ` adds no
restriction. The normal-scheme dependency was added for the already existing definition.
The rereading found the missing direct forgetful instance and compiler warnings described
above; those were repaired without changing the mathematical statement.
