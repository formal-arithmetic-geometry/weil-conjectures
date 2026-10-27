## Worker report

The module `Sheaf.AlgebraicGeometry.SplitTorusFiniteTorsionNormalizerDetection` states
`AlgebraicGeometry.split_torus_exists_finite_torsion_normalizer_detection`.
Its sole theorem has a `sorry` proof. The docstring gives all eight accepted proof steps,
including the universal Laurent-support bound, the residue basis, inverse conjugation,
and gluing over arbitrary test schemes. No definitions, new nodes, dependency repairs,
or statement corrections are required. The node changes only in `lean`.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Any commutative ring A, S = Spec A | `(A : Type u) [CommRing A]`, with base `Spec (.of A)` throughout. |
| G and T are S-group schemes | `(G T : Over (Spec (.of A))) [GrpObj G] [GrpObj T]`. `GrpObj` supplies multiplication, identity, inverse and their diagrams. |
| G → S smooth | `[Smooth G.hom]`. |
| G → S affine | `[IsAffineHom G.hom]`. |
| G → S of finite presentation | `[LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom] [QuasiSeparated G.hom]`, precisely the dependency convention, even though some properties follow from the other hypotheses. |
| Integer rank r ≥ 0 | `(r : ℕ)`, including zero. |
| T identified with G_m^r as a group scheme | `hT : Nonempty (yonedaGrpObj T ≅ relativeSplitTorusFunctor (Spec (.of A)) r)`. This is an isomorphism of group-valued functors, not of underlying sets. The dependency defines the right side as the finite product of units of global sections. Yoneda identifies this with the asserted group-scheme splitting. |
| T ↪ G is a closed subgroup | `(i : T ⟶ G) [IsMonHom i] [IsClosedImmersion i.left]`. The first class makes the map a group homomorphism; the second makes its underlying scheme map a closed immersion, hence injective on every test scheme's points. |
| T[n] = ker [n] with inherited group law | On each test scheme the literal subset `{t | t ^ n = 1}` of `V ⟶ T`. Group operations here are Mathlib's operations induced by `GrpObj T`. Under `hT` it is the tuples of units satisfying t_j^n = 1, exactly the functor represented by the displayed Laurent quotient in the node. No arbitrary kernel object is chosen. |
| There exists an integer n ≥ 1 | `∃ n : ℕ, 1 ≤ n ∧ ...`. |
| One n works for every W and g ∈ G(W) | The existential precedes `∀ (W : Over (Spec (.of A))) (g : W ⟶ G)`. |
| g T_W g⁻¹ = T_W as subgroup functors | The first universally quantified equality of `Set.range`: on each `f : V ⟶ W`, conjugate all images `t ≫ i` by `f ≫ g`, and compare with the full image of i. |
| g T[n]_W g⁻¹ = T[n]_W as subgroup functors | The second universally quantified equality of set images of `{t | t ^ n = 1}` under conjugation and inclusion. Both directions are joined by `↔`. |
| K_W = K ×_S W | For any `V → W`, its V-valued points over W are canonically `Hom_S(V,K)` by the fibre-product universal property. The statement uses these points directly; f specifies the W-structure. This includes all W-schemes, rather than only affine tests. |
| Arbitrary base change | Any further base change and its test schemes compose to S-schemes already covered by the same n. No n is reselected depending on W or g. |
| No invertibility or Noetherian assumptions | Neither is present; no field, reducedness, characteristic or nontriviality hypotheses are present. |

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map` (scheme and affine-spectrum dependencies).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` and its `finitePresentation_appLE`
  field (the latter is the proof leaf on affine opens).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `QuasiSeparated`:
  `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.QuasiSeparated`, implementing
  `def-weil-pbc-scheme-conventions` (a convention node, not a separate declaration).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.RelativeTorus`:
  `AlgebraicGeometry.relativeSplitTorusFunctor` (the recorded relative-torus
  dependency's split functor) and `IsRelativeTorus` (read; the hypothesis here is
  the specified global splitting, so using only `IsRelativeTorus` would lose it).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`;
  their universal property explains the direct functor-of-points formulation.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, publicly available through the
  torus dependency: `GrpObj`, `yonedaGrpObj`, `CategoryTheory.Hom.group` and
  `IsMonHom` for the group-object functor of points and subgroup homomorphism.

Proof-only imports retain the available proof-dependency interfaces:
`Mathlib.RingTheory.FinitePresentation` (`Algebra.FinitePresentation`,
`Algebra.FinitePresentation.ker_fg_of_mvPolynomial`),
`Mathlib.RingTheory.Ideal.Quotient.Operations` (`Ideal.Quotient.mkₐ` and the
quotient algebra), `Mathlib.AlgebraicGeometry.Gluing`
(`Scheme.Cover.glueMorphisms` and uniqueness),
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
(`ΓSpec.locallyRingedSpaceAdjunction`), and
`Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`
(`ringDiagonalizableGroup`, `ringDiagonalizableGroupMap`).
The genuine proof node `lem-sfb-subgroup-algebra-coset-presentation` has neither
`lean` nor `mathlib_match` in the read repository; no module for it can be imported.
It is not needed to type this statement and is explicitly retained in the proof docstring.

### Edge cases

- A = 0: there is no `Nontrivial A` binder. Every S-scheme is empty, and both
  subgroup functors are trivial. A positive n exists.
- r = 0: `Fin 0` is empty and the split functor is the trivial group. Both
  normalizer conditions hold for every g; n = 1 is permitted.
- n = 1 is allowed by the existential, but not asserted to work for every torus;
  for a nonnormal positive-rank torus its trivial 1-torsion cannot detect it.
- Characteristic dividing n and nonreduced tests: the condition is `t ^ n = 1`
  on every scheme V. It detects infinitesimal torsion as a functor, rather than
  replacing it by geometric points or assuming n invertible.
- W and V may be empty, nonaffine, disconnected or nonreduced. Quantification
  over `Over S` and all maps V → W imposes none of those restrictions.
- Universes: all schemes and the base ring use the explicit common universe u,
  with all binders explicit and auto-implicit disabled. Test schemes range over
  the same full category of schemes as the recorded torus functor.

### Searches

The prescribed msearch wrapper wrote the raw results into `searches.jsonl`:

- LeanFinder: `One finite torsion subgroup of a split torus detects its normalizer in an affine group scheme over any commutative ring after every base change`.
  Eight hits: Hilbert 90, absolute Galois commutators, PreGalois stabilizers and
  open subgroups, torsion extensions, finite cyclic representations. No match.
- Loogle: `"normalizer", "torsion"`. Zero hits.
- Mathlib grep in AlgebraicGeometry: `normalizer.*torsion|torsion.*normalizer`.
  Zero hits.
- LeanSearch: `A split torus normalizer in an affine group scheme of finite presentation is detected by one finite torsion subgroup universally over the base ring`.
  Eight hits: `Subgroup.setNormalizer`, abstract torsion groups, additive
  normalizers, `NormalizerCondition`, `AddSubgroup.torsionBy`. None asserts
  a uniform torsion level for group schemes.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `normalizer.*torsion|torsion.*normalizer|finite.torsion.normalizer` and the
  item id: no match. The same new declaration name was searched in those trees,
  Mathlib and `dag/lean_names_upstream.json`: no collision.
- Read `RelativeTorus.lean` in full and inspected related torus modules for the
  existing group-object and split-functor interfaces. Reused them directly.

Source consulted online: Conrad's linked PDF, especially Example 2.1.9 (p.62)
and the surrounding universal torsion-density discussion. The item's accepted
proof supplies the explicit finite-support bound that avoids Noetherian descent.
No statement is disputed and no fault was found in the node.

### Validation

`scompile.py Q112 lem-sfb-split-torus-finite-torsion-normalizer-detection <module>`
compiled both the sandbox probe and the actual library module without errors or
warnings. Each used the required 60-second per-file limit; actual library module
compilation took 4.7 seconds. No local or global build was run.

## Second reading by Q112

Performed a separate clause-by-clause rereading of the node and completed module
in this worker session; no other agent was launched, as instructed by the dispatcher.
The maintainer's independent review remains the independent reading.

Checked that `hT` is a group-valued natural isomorphism to the dependency's precise
split functor, that i is both a group homomorphism and a closed immersion, and that
all three finite-presentation properties are retained. Checked the scope of n:
it is outside W, g, V and f. Checked that the two sides are equality of sets on
every V → W, so both inclusions are present and neither condition is merely a
single set of W-valued points. Torsion uses powers in T(V), before inclusion into
G(V), and hence is exactly the kernel in the node. No extra finite, flat, field,
Noetherian, reduced, nonempty or invertibility condition was introduced. The
Laurent quotient describes the same kernel functor under hT and is documented,
without a duplicate definition of a representing scheme. No mismatch required
changing the node or module.
