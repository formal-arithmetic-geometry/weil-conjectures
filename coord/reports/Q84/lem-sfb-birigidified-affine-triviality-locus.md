## Worker report

The module `Sheaf.AlgebraicGeometry.BirigidifiedAffineTrivialityLocus` states
`AlgebraicGeometry.exists_finite_extension_isClopen_birigidified_affine_triviality_locus`.
The sole proof is `sorry`; no definitions or auxiliary theorems are introduced.
The item's only changed field is `lean`.

Source read: Ning Guo, *Divisors on coherent schemes and homogeneous spaces*, March 31,
2026 author version, Proposition 5.2, proof of Claim 5.2.1, printed pp.12-13,
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . The node is the
smooth affine two-axis family input extracted from that argument, not the proper
Stacks theorem of the cube. The source paragraph constructs the rigidified family
and asserts clopenness; the node's five-step proof supplies the detailed affine
assembly. All five steps and their named dependencies are in the theorem docstring.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| F is a field | `{F : Type u} [Field F]` |
| U,V,T are F-schemes | `U V T : Over (Spec (.of F))`; their structure morphisms are `.hom` |
| U and V affine | `[IsAffine U.left] [IsAffine V.left]` |
| U and V finite type | `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]`, and the same pair for V |
| U and V smooth | `[Smooth U.hom] [Smooth V.hom]` |
| U and V geometrically integral | `[GeometricallyIntegral U.hom] [GeometricallyIntegral V.hom]` |
| Rational points u,v over F | `u : 𝟙_ (Over (Spec (.of F))) ⟶ U` and the analogous v; an Over morphism imposes exactly the section equation |
| T smooth | `[Smooth T.hom]` |
| T separated, diagonal closed immersion | `[IsSeparated T.hom]`; the class is defined by `IsClosedImmersion (pullback.diagonal T.hom)` |
| T finite type | `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom]` |
| T geometrically integral | `[GeometricallyIntegral T.hom]` |
| M an invertible module on U × V × T | `M : ((U ⊗ V) ⊗ T).left.Modules` and `[M.IsInvertible]`; the Over cartesian tensor is the fibre product |
| Trivial pullback on {u} × V × T | `hu`, tensor pullback along `(lift (lift (toUnit (V ⊗ T) ≫ u) (fst V T)) (snd V T)).left`, isomorphic to `SheafOfModules.unit _` |
| Trivial pullback on U × {v} × T | `hv`, tensor pullback along `(lift (lift (fst U T) (toUnit (U ⊗ T) ≫ v)) (snd U T)).left`, isomorphic to the structure sheaf |
| There exists a field extension K/F | `∃ (K : Type u) (_ : Field K) (_ : Algebra F K), ...`; `algebraMap F K` is its ring homomorphism |
| K finite-dimensional over F | `Module.Finite F K` (finite generation over a field is precisely finite-dimensionality) |
| Base-changed parameter T_K | `pullback (C := Scheme.{u}) T.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))` |
| Base-changed total family | Pull back `f = (snd (U ⊗ V) T).left` along `g = pullback.fst T.hom (Spec.map ...) : T_K ⟶ T`; its total scheme `pullback f g` is canonically `U_K ×_K V_K ×_K T_K` |
| Actual fibre over κ(t) | `(pullback.snd f g).fiberι t`; Mathlib defines its source to be the pullback along `T_K.fromSpecResidueField t`, not an algebraic closure of κ(t) |
| The pullback (M_K)_t | `tensorPullback ((pullback.snd f g).fiberι t ≫ pullback.fst f g)` applied to M; tensor-pullback composition identifies this with the two successive pullbacks |
| E consists exactly of points whose fibre is trivial | The displayed set comprehension tests `Nonempty (... ≅ SheafOfModules.unit _)` |
| E open and closed | `IsClopen` of exactly that set |

Dependency interfaces read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme` and `def-weil-affine-spectrum`: `AlgebraicGeometry.Scheme`,
  `Spec`, and `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sbc-smooth-morphisms`: `Smooth` in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-pc-geometrically-irreducible`: `GeometricallyIntegral` in
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, exactly integral after field base change.
- `def-pc-rational-point`: the recorded `Scheme.Hom.baseChangeFieldPoint` in
  `WeilConjectures.AlgebraicGeometry.DensePoints` was read. This theorem needs only
  rational sections, represented by morphisms from the cartesian unit in Over;
  no construction of their further base changes is needed in the statement.
- `def-sc-invertible-module`: `Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `def-pc-fibre-product`: `Limits.pullback`, `.fst`, `.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; the cartesian
  structure on Over is the same chosen pullback construction.
- `def-pc-module-pullback`: the recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
  Its canonical composition `tensorPullbackSectionComp` identifies the composite
  pullback used here with successive pullbacks. No Mathlib `Modules.pullback` is used.
- `def-weil-residue-field`: `Scheme.residueField`, `Scheme.fromSpecResidueField` in
  `Mathlib.AlgebraicGeometry.ResidueField`, used by `Scheme.Hom.fiberι` in
  `Mathlib.AlgebraicGeometry.Fiber`.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.

Public imports give the statement dependencies. Plain imports give all recorded
proof-dependency modules, including the Mathlib leaves for smoothness, finite-type
permanence and Noetherianity. Four proof dependencies have no recorded declarations:
`lem-sfb-affine-product-algebraic-equivalence`,
`lem-sfb-constant-variety-picard-detection`,
`lem-sfb-normal-noetherian-generic-line-pullback`, and
`lem-trf-fp-module-limit-isomorphism-descent`; these are named in the proof docstring
and have no import to add yet. They are not prerequisites for typing this statement.

Edge cases checked before writing: the field extension may be the identity, in
particular in the empty-locus case; it need not be separable or purely inseparable.
No algebraic closedness, characteristic restriction, or rational point of T is
assumed. Arbitrary (including nonclosed) points t and their own residue fields
are tested. No affine or proper hypothesis is imposed on T; no proper hypothesis
is imposed on U,V. Geometric integrality already rules out the empty factors and
parameter, so no extra nonemptiness or connectedness binder is added. Dimension
zero and the structure sheaf M are included. All schemes, the ground field and the
finite extension use the arbitrary common universe u; finite extensions admit a
model in that universe. All variables and universes are explicit; auto implicits
and relaxed auto implicits are disabled.

Searches made (all via the prescribed wrapper or read-only rg):

- LeanFinder: “The trivial fibre locus of a line bundle on a product of two smooth
  affine geometrically integral varieties rigidified along two rational point axes
  is clopen after finite field extension”. Eight results, about clopen subsets of
  prime spectra and locally constant functions; none states the line-bundle result.
- Loogle: `"IsInvertible", "pullback"`. Two differential-vector-field pullback
  lemmas, unrelated to invertible sheaves.
- Mathlib grep: `rigidif|trivial.*locus|locus.*trivial` in AlgebraicGeometry.
  Zero hits.
- LeanSearch: “A doubly rigidified line bundle on the product of two smooth affine
  varieties has a clopen trivial fibre locus after finite field extension”. Eight
  topological vector/fibre-bundle trivialization results, no match.
- Project and upstream rg: `birigidified|doubly rigidified|affine.*triviality.*locus|isClopen.*[Tt]rivial`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.
  The exact item id has no hit in `lean/WeilConjectures` either.
- Broader rigidification/Picard/triviality searches located
  `WeilConjectures.AlgebraicGeometry.TheoremOfCube`,
  `WeilConjectures.AlgebraicGeometry.Seesaw` and
  `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube`; their signatures were read.
  They require proper factors and do not state this affine result.

No statement correction, dependency repair, new node, or statement dispute.
Validation: scompile.py compiled both sandbox and library-name versions cleanly
(3.6 s and 9.0 s respectively). The first compiler probe needed an explicit
`(C := Scheme.{u})` on the pullback occurring as a point type, since otherwise
elaboration tried the category of types; this is now explicit.

## Second reading by Q84

Independent second reading by the maintainer's reviewer (cc review service), replacing the
worker's final self-check, which was not an independent second reading.

Node statement as a list, with the Lean rendering and verdict:

1. F a field: `{F : Type u} [Field F]` (Mathlib `Field`). OK.
2. U, V affine F-schemes of finite type: `U V : Over (Spec (.of F))`, `[IsAffine U.left]`,
   `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]` (the def-weil-finite-type-morphism record
   states finite type as exactly this conjunction), same for V. OK.
3. U, V smooth and geometrically integral: `[Smooth _.hom]`, `[GeometricallyIntegral _.hom]`;
   Mathlib `GeometricallyIntegral f` is `geometrically IsIntegral f` = integral after every base
   change to a field `Spec K → Spec F` (recorded declaration of def-pc-geometrically-irreducible). OK.
4. F-rational points u, v: morphisms `𝟙_ (Over (Spec (.of F))) ⟶ U`, i.e. sections of the
   structure morphism (def-pc-rational-point). OK.
5. T smooth, separated, finite type, geometrically integral: `[Smooth T.hom] [IsSeparated T.hom]
   [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [GeometricallyIntegral T.hom]`; no affineness,
   properness or rational point of T is assumed. OK (LFT is implied by Smooth; not stronger).
6. M invertible on U ×_F V ×_F T: `M : ((U ⊗ V) ⊗ T).left.Modules`, `[M.IsInvertible]`; the
   cartesian structure on `Over` is the chosen pullback. OK.
7. Trivial on {u} × V × T: `hu`, tensor pullback along `lift (lift (toUnit ≫ u) (fst V T)) (snd V T)
   : V ⊗ T ⟶ (U ⊗ V) ⊗ T`, coordinates (u, id_V, id_T); iso to `SheafOfModules.unit _`. OK.
8. Trivial on U × {v} × T: `hv`, coordinates (id_U, v, id_T). OK.
9. ∃ finite K/F: `∃ (K : Type u) (_ : Field K) (_ : Algebra F K), Module.Finite F K`. OK
   (finite extensions have models in universe u; the existential is not weakened).
10. T_K, M_K, (M_K)_t: T_K = `pullback T.hom (Spec.map (algebraMap F K))`; the family
   Z ×_T T_K ≅ U_K ×_K V_K ×_K T_K via `pullback (snd (U ⊗ V) T).left (pullback.fst …)`; its fibre
   over t ∈ T_K is Mathlib `fiberι` (pullback along `Spec κ(t) → T_K`, the actual residue field,
   def-weil-residue-field), and the composite with `pullback.fst` back to Z pulls M back to the
   fibre, which is (M_K)_t up to the canonical iso (tensorPullback composition; triviality is
   iso-invariant). OK.
11. E(M_K) clopen in |T_K|: `IsClopen {t | Nonempty (… ≅ SheafOfModules.unit _)}` over all points
   of T_K (including non-closed). OK.

Edge cases: K = F (identity extension) allowed; empty locus allowed; no characteristic,
perfectness, algebraic closedness or separability assumption (this is exactly the corrected,
L-reviewed statement, whose need for K is the imperfect-field counterexample); geometric
integrality already excludes empty U, V, T; dimension 0 and M = O included. Universes: a single
universe u, all bound; no auto-implicits.

Records: item node differs from live only in the new `lean` field; `lean.statement` is verbatim
in the file. Statement dependencies' recorded declarations (Scheme, Spec, LocallyOfFiniteType /
QuasiCompact, Smooth, GeometricallyIntegral, IsInvertible, pullback, tensorPullback,
residueField / fiberι, Algebra) are those used; Mathlib `Modules.pullback` is not used. All
imported modules exist on the live tree. One proof `sorry`, no definitions. Docstrings carry the
Guo place, the blueprint id and the five proof steps.

Searches: the declaration name and module name do not occur in live `lean/Sheaf` or
`lean/WeilConjectures`; the existing TheoremOfCube / Seesaw / GeneralTheoremOfCube statements
require proper factors and do not state this affine result.

Mismatches found: none in the mathematics or the records. Change: this section only.
