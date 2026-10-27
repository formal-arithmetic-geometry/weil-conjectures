## Worker report

The module `Sheaf.AlgebraicGeometry.FlatIntegralFreeSurjectionIsoLocus` states
`AlgebraicGeometry.Scheme.exists_flatIntegralFreeSurjectionIsoLocus`, with one
`sorry` and no definitions or additional theorems. The node is unchanged except
for its `lean` record. No new nodes, dependency repairs, statement correction or
STATEMENT-DISPUTED issue is needed.

I read the node, all twelve statement dependencies and their Lean records,
the recorded source declarations, and Stacks `flat.tex`, Tags 05PF
(`theorem-flattening-map`, lines 6671ff), 05K5
(`lemma-flat-geometrically-integral-fibres-pure`, lines 5124ff), and 05PE
(`lemma-flattening-module-map`, lines 6646ff). The theorem is the finite-free
source case of 05PF; 05K5 gives purity. Its docstring retains the seven-step
accepted proof, including the coefficient-ideal finite-generation argument.

Hypothesis and clause correspondence:

- Schemes and their map: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Affine: `[IsAffineHom f]`.
- Flat: `[Flat f]`, equivalent to flatness of each stalk map by
  `Flat.iff_flat_stalkMap`.
- Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  `[QuasiSeparated f]`, exactly the three conditions explicitly specified in
  the node. No Noetherian, separated, smooth or proper hypothesis is imposed.
- All fibres nonempty and geometrically integral: `[GeometricallyIntegral f]`.
  `GeometricallyIntegral.iff_geometricallyIntegral_fiber` identifies this with
  the fibrewise condition. The class requires integral pullback by every field
  point, and `IsIntegral.nonempty` includes nonemptiness. There is no redundant
  extra surjectivity assumption and no restriction to closed points or to
  algebraically closed fields.
- Rank `n ≥ 0`: `(n : ℕ)`, including zero.
- The finitely presented quasi-coherent module: `(G : X.Modules)` with
  `[G.IsQuasicoherent] [G.IsFinitePresentation]`. These are the dependency's
  actual sheaf predicates; coherence is not substituted for finite presentation.
- The specified source `O_X^{⊕n}`: `SheafOfModules.free
  (R := X.ringCatSheaf) (ULift.{u} (Fin n))`. By its definition this is the
  coproduct of exactly `n` copies of the unit sheaf. `ULift` only places the
  finite index in the coefficient universe, retaining zero and every rank.
- The surjective module-sheaf map: `(q : ... ⟶ G) [Epi q]`. Surjectivity is
  surjectivity of a sheaf map (locally lifting sections, or surjectivity on
  stalks); no surjectivity on every open's section module is assumed.
- The representing closed immersion: `∃ (Z : Scheme.{u}) (i : Z ⟶ S),
  IsClosedImmersion i ∧ ...`.
- Its finite presentation: `LocallyOfFinitePresentation i ∧ QuasiCompact i ∧
  QuasiSeparated i`, retaining the full three-part meaning.
- Every test scheme and base map: `∀ (T : Scheme.{u}) (h : T ⟶ S)`.
  All schemes use the fixed arbitrary universe `u`, with no separate smaller
  test universe. No affineness, finiteness, reducedness or nonemptiness is
  required of a test scheme.
- `X_T = X ×_S T` and its map to `X`: `pullback f h`, `pullback.fst f h`.
- The actual tensor pullback of the given map: `(Modules.tensorPullback
  (pullback.fst f h)).map q`. Its target is the actual tensor pullback of `G`;
  its source is the actual tensor pullback of the rank-`n` free sheaf, canonically
  the rank-`n` free sheaf on `X_T`. Isomorphism is invariant under that canonical
  source identification, so no separately chosen comparison is necessary.
- Factorization if and only if invertibility: `((∃ g : T ⟶ Z, g ≫ i = h) ↔
  IsIso (...))`.
- Unique whenever a factorization exists: `∀ (g₁ g₂ : T ⟶ Z),
  g₁ ≫ i = h → g₂ ≫ i = h → g₁ = g₂`. This is stated independently of the
  equivalence, so uniqueness is not merely existence of a unique map in place
  of existence while leaving spurious other maps unexcluded.

Dependency declarations used (each recorded module is publicly imported):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, which exposes
  `AlgebraicGeometry.QuasiCompact` (defined in Morphisms.QuasiCompact).
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`.
- `def-pc-geometrically-irreducible`:
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  `AlgebraicGeometry.GeometricallyIntegral`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  Mathlib's `SheafOfModules.IsQuasicoherent`. The bundled conjunction and the
  coherence predicate are not used, since neither is the requested hypothesis.
- `def-weil-pbc-module-finite-type-presentation`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.IsFinitePresentation` (defined in Sheaf.Quasicoherent and
  exposed also by the quasi-coherence dependency).
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, exposing the real
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. I read its actual tensor
  object, tensor map and functor definitions, rather than using an arbitrary
  map or an abstract choice of pullback functor.

The finite free sheaf is Mathlib's existing `SheafOfModules.free`, from
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`. All already stated proof
prerequisites' modules are imported privately unless they are already public
statement imports. The proof-only node
`lem-trf-closed-immersion-finite-presentation-ideal` has no recorded declaration
or Mathlib match at inspection, so has no module to import; no new statement
notion depends on it.

Edge cases checked against the mathematical statement before writing:

- `n = 0`: the source is zero and epimorphy forces `G = 0`; every pullback is
  invertible and the representative is `S`.
- Empty base: affineness forces the source empty, and the empty closed
  subscheme represents the vacuous family. Empty test schemes are included.
- Identity family and `G = O_S/(a)` in rank one: the representative is the
  closed subscheme cut out by `(a)`, which confirms the criterion is a closed
  base-change condition rather than the open pointwise isomorphism locus.
- Nilpotent `a`, arbitrary nonreduced test schemes, and zero rings are included;
  the criterion detects the ideal itself, not its radical.
- `q` already invertible gives `Z = S`; no condition assumes positive rank,
  nonempty base, finite base-module rank of the affine algebra or Noetherianity.

Searches actually run with `msearch.py Q32 <item>`:

- LeanFinder: "For an affine flat finitely presented morphism with geometrically
  integral nonempty fibres, a finite free quotient is universally an isomorphism
  on a finitely presented closed subscheme of the base". Eight results, including
  `UniversallyOpen.of_flat`, `Flat` and `Flat.isIso_of_surjective_of_mono`;
  none represents the sheaf-quotient base-change isomorphism condition.
- Loogle: `"IsClosedImmersion", "IsIso"`. Seven results about scheme closed
  immersions and isomorphisms, including
  `IsClosedImmersion.isIso_iff_ker_eq_bot`; none is this relative sheaf theorem.
- Mathlib grep: `flattening|isoLocus|isomorphism.*locus` in AlgebraicGeometry:
  zero hits.
- LeanSearch: "A surjective morphism from a finite free sheaf on a flat affine
  family with geometrically integral fibres becomes an isomorphism exactly on
  a closed finitely presented subscheme of the base". Eight results about flat
  monomorphisms, closed immersions and surjective scheme maps, no exact match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `flattening|isoLocus|isomorphism.*locus|free.*surjection`: unrelated flattening,
  derived functor iso loci, finite-free resolutions and universal scheme-map
  isomorphism loci; no declaration with this statement. In particular the
  affine free-map zero locus theorem concerns zero pullbacks of a map on an
  affine base and is not this quotient theorem.
- Direct `grep -rn` for the item's exact id in `lean/WeilConjectures`: no hits.
- Direct name search for `FlatIntegralFreeSurjectionIsoLocus` and
  `exists_flatIntegralFreeSurjectionIsoLocus` in both project roots, Mathlib and
  `dag/lean_names_upstream.json`: no pre-existing declaration.

Validation: `scompile.py Q32 lem-sfb-flat-integral-free-surjection-iso-locus
<module>` compiled the module in both sandbox and library module-name modes
without errors or warnings (19.5 s and 10.4 s). All variables and the single
universe are explicit, with `autoImplicit` and `relaxedAutoImplicit` disabled.
No Lean line exceeds 100 characters.

## Second reading by Q32

I reread the written signature against the complete node and the source after
compilation. The affine/flat/finite-presentation conditions, geometric fibre
condition, rank, module, sheaf epimorphism, closed finite-presentation conclusion,
arbitrary test map, actual tensor pullback, both directions and uniqueness all
match as detailed above. No mismatch or correction was found. The free sheaf's
universe lift preserves its finite basis, and the pullback projection is the
first projection to `X`, not the second projection to the test base. Invertibility
is of the supplied map after tensor pullback, not existence of an unrelated
isomorphism between its objects. No independent worker was started, as the
dispatcher explicitly prohibits that; the maintainer supplies the independent
review specified by this assignment.
