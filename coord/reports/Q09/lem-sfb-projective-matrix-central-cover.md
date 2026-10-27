## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover` states
`AlgebraicGeometry.ProjectiveMatrixCentralCover.exists_presentation`, with `sorry` as its
entire proof. It asserts existence of an affine group scheme with the full fpqc scalar
quotient universal property and all the node's central-cover and geometric properties.
No object is defined by choosing a witness of this existence theorem. The helper
`Presentation` is a Prop bundling this node's clauses, and `CompatibleExtension` is a
fully written Prop specifying its field-extension comparisons. The other helpers are the
actual scalar map and the canonical Spec map of a field extension. No independent
mathematical notion, new DAG node, dependency repair, or statement correction is needed.
Only the item's `lean` field changes.

Hypotheses and initial objects:

- A field k is `(k : Type u) [Field k]`, explicitly declared among the section variables.
- The matrix size is `(r : ℕ)` with the sole numerical hypothesis `(hr : 2 ≤ r)`.
  There is no NeZero binder or assumption about the characteristic. The positivity needed
  by the existing roots-of-unity inclusion is derived from hr in `rootsScalar` using
  existing natural-number lemmas.
- GL is `GeneralLinearGroup (LinearGroupSchemes.Index.{u} r) k`. Its coordinate ring is
  exactly the existing localization of the multivariate polynomial ring at the generic
  matrix determinant. `Index r = ULift (Fin r)` has exactly r elements; the lift places
  its indices in the field's ambient universe without changing the matrix size.
- SL is `LinearGroupSchemes.specialLinear k r`, the existing spectrum of
  `SpecialAlgebra k r = k[x_ij]/(det X - 1)`, with its specified matrix group law.
  `LinearGroupSchemes.inclusion k r` is the existing quotient-induced inclusion into GL.
- Gm and μr are the recorded `StandardGroupSchemes.multiplicative k` and
  `StandardGroupSchemes.roots k r`, with their Laurent and polynomial quotient rings.
- All morphisms live in `Over (Spec (.of k))`. `Grp (Over ...)` bundles a scheme with its
  group-object structure. There is no arbitrary additional action or supplied PGL model
  in the hypotheses.

Every conclusion is matched as follows (field names are in `Presentation`):

| Node clause | Lean rendering |
| --- | --- |
| An affine group scheme PGL represents the fpqc quotient | `∃ (G : Grp (Over ...)) ...`, `affine`, `quotient_sheaf`, `quotient_universal` |
| The quotient is the sheafification of GL(T)/Γ(T,O)ˣ | `quotient_universal` quantifies over every fpqc sheaf F and every scalar-invariant natural map `a : yoneda.obj GL ⟶ F.obj`, requiring a unique factorization through `yoneda.map π`. Together with `quotient_sheaf` this is precisely the sheafification universal property of the pointwise orbit presheaf. No sheafification-existence instance on an arbitrary large site is assumed. |
| The scalar subgroup is the usual Gm | `scalar` is Spec of `Matrix.GeneralLinearGroup.evalAlgHom` evaluated at the scalar matrix tI over `LaurentPolynomial k`. Its values are the diagonal Laurent generator and zero off diagonal. Thus its T-points are the usual scalar units on every test scheme. |
| GL → PGL is the quotient group map | `quotient_hom : IsMonHom π`; its universal property fixes the quotient map, not just an abstract isomorphic target |
| It is faithfully flat | `gl_flat : Flat π.left`, `gl_surjective : Surjective π.left` |
| It is a Gm-torsor | `gl_torsor` supplies an isomorphism `GL ⊗ Gm ≅ pullback π π`; its first projection is g and its second projection is `g * scalar(z)` |
| q is the restriction to SL | Every occurrence of q is the literal composite `LinearGroupSchemes.inclusion k r ≫ π`, with `sl_hom` asserting its group-homomorphism property |
| q is finite locally free of rank r | `sl_finite_locally_free : q.left.IsFiniteLocallyFreeOfDegree r` uses the existing finite/flat/locally-finite-presentation/fibre-degree class |
| The affine/direct-image formulation | `sl_affine : IsAffineHom q.left`, and `sl_structure_rank` states that the actual pushforward of `SheafOfModules.unit SL.left.ringCatSheaf` is `IsFiniteLocallyFreeOfRank r` |
| q is surjective | `sl_surjective : Surjective q.left` |
| Its kernel is μr acting by scalar matrices | `kernel` gives an isomorphism `roots k r ≅ GrpObj.ker q` respecting its inclusion j; `scalar_kernel` fixes `j ≫ inclusion` to be the existing Laurent quotient into Gm followed by the actual scalar map |
| The kernel is central | `central` says `Commute g (z ≫ j)` for all T, all SL(T) points g, and all μr(T) points z |
| q is an fpqc covering | `sl_fpqc : Presieve.singleton q.left ∈ Scheme.fpqcPrecoverage G.X.left` |
| (g,z) ↦ (g,gz) is the specified SL torsor isomorphism | `sl_torsor` supplies `SL ⊗ roots ≅ pullback q q`, fixing both projection composites as g and `g * (z ≫ j)` |
| SL and PGL are smooth | `sl_smooth`, `pgl_smooth`, using `AlgebraicGeometry.Smooth` of their structure maps |
| Both are finite type | `sl_finite_type`, `pgl_finite_type`, each `LocallyOfFiniteType ... ∧ QuasiCompact ...` |
| Both are geometrically connected | `sl_geometrically_connected`, `pgl_geometrically_connected`, using Mathlib's `GeometricallyConnected`; over a field this is equivalent to connectedness after algebraically closed field extensions |
| Both have Krull dimension r²−1 | `sl_dimension`, `pgl_dimension`, with `topologicalKrullDim` and the natural number `r ^ 2 - 1` cast into `WithBot ℕ∞` |
| Descriptions commute with field extension | The final quantifier over `K`, `[Field K]`, `[Algebra k K]` supplies a presentation over K and `CompatibleExtension k r K ...` relating it to the original one |
| The same maps and presentations after extension | `CompatibleExtension` supplies comparisons for GL, SL, μr, PGL and Gm. The GL/SL matrix coordinates and μr/Gm generators are fixed by explicit equations on global sections; diagrams commute with π, inclusion, j and the scalar map. These determine the restricted map q, kernel map, and both torsor isomorphisms after extension. |
| No invertibility assumption on r | There is no `IsUnit (r : k)`, `CharZero`, separability, perfectness, or reducedness hypothesis anywhere. |

Why the sheafification clause is exact: natural maps from the pointwise quotient
presheaf to a presheaf F correspond bijectively to natural maps from GL to F constant on
scalar orbits. The invariant condition is written for every `T : Over (Spec k)` and
all its GL and Gm points. The GL torsor projection equations also imply that π itself
is scalar invariant. The two fields `quotient_sheaf` and `quotient_universal` therefore
say exactly that the represented presheaf is the fpqc sheafification of those orbits.
This formulation uses the universal property recorded in def-weil-pbc-sheafification;
it does not confuse the quotient presheaf with its sheafification or replace PGL by
GL(k)/kˣ. In particular it does not assert that SL(k) → PGL(k) is surjective.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the explicit comparisons also use `Scheme.ΓSpecIso`.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, the Leibniz determinant used by the
  existing coordinate presentations.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, the existing affine-local/stalkwise class.
- `sk-def-av-group-scheme`: the closed upstream audit gives `CategoryTheory.GrpObj.ker`
  in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` and
  `Scheme.Hom.finrankΓ` in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
  The full group-object and kernel declarations/docstrings were read. Here the group
  objects use the existing `Grp`/`GrpObj`, and the kernel is literally `GrpObj.ker`.
  `finrankΓ` is not needed separately since this statement fixes the degree through the
  existing finite-locally-free class.
- `def-weil-pbc-fpqc-covering`: `Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; the quotient uses its generated `fpqcTopology`
  restricted to the slice by the existing `GrothendieckTopology.over`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, as the recorded conjunction.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, with its full `WithBot ℕ∞` codomain.
- `def-sc-general-linear-group`: the recorded module
  `Sheaf.AlgebraicGeometry.LinearGroupSchemes`, including `Index`, `SpecialAlgebra`,
  `specialMatrix`, `specialLinear`, `specialGroup`, `inclusion`, and the upstream
  `AlgebraicGeometry.GeneralLinearGroup`. Their entire source and docstrings were read.
- `def-sc-gm-ga`: the recorded module `Sheaf.AlgebraicGeometry.StandardGroupSchemes`,
  especially `affine`, `map`, `multiplicative`, `roots`, `rootsAlgebra`,
  `rootsCoordinate`, `rootsInclusion`. Their signatures, group laws, and coordinate
  constructions were read. The existing roots inclusion is specialized with the
  positivity proof supplied by hr, rather than redeclared.
- The proof dependency `def-pc-finite-locally-free` is the recorded
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`.
  The direct-image clause uses the existing `Scheme.Modules.pushforward`,
  `SheafOfModules.unit`, and `SheafOfModules.IsFiniteLocallyFreeOfRank`, matching the
  recorded `finiteLocallyFree_structureSheaf_properties` signature.
- Geometric connectedness uses `Mathlib.AlgebraicGeometry.Geometrically.Connected`;
  no private predicate is introduced. The field extension uses existing `Over.pullback`.

All recorded non-Mathlib proof-dependency modules, including closed upstream audit
records, are imported with plain `import` when not already needed publicly. The only
unrecorded proof dependency is `lem-sfb-projective-frames-pgl`; it has neither a Lean
record nor a closed upstream declaration in the supplied DAG, so no import is available.
It is needed for the proof plan only: no unstated frame or PGL construction is used in
the signature. The module docstring and theorem docstring include the full ten-step
proof plan, including the normalized-entry algebras, their monic bases, and the cofactor
charts. Existing Mathlib proof matches are imported through their owning modules.

Sources checked: the supplied node's ten proof steps and dependency records; Milne's
local `literature/milne-algebraic-groups_iAG2017.pdf`, Examples 2.42 and 5.49,
Propositions 5.23--5.25 and 7.15, read with pdftotext; and the node's primary
[corrected 2022 text](https://www.jmilne.org/math/Books/iAG2022.pdf), the same numbered
places and Corollary 5.27, read online. The quotient, torsor, and kernel assertions agree.
No statement fault or mathematical dispute was found.

Edge cases checked before writing and again after elaboration:

- r=2 in characteristic 2, and generally char(k) dividing r: μr can be nonreduced,
  but the full quotient scheme and all test schemes are retained; q is not claimed étale.
- Nonreduced k-algebras and test schemes: μr is not replaced by its reduced subscheme
  or its geometric points, and centrality and torsor identities are scheme statements.
- Nonaffine T: sheaf invariance and the universal property quantify over the whole slice
  category, not just affine spectra. GL(T) and Gm(T) are represented scheme-valued points.
- Empty T and the zero test algebra are included. No Nonempty or nontrivial-algebra
  assumption appears on test schemes or their global section rings.
- r=0 and r=1 are exactly the ranks excluded by the original condition r≥2; no stricter
  lower bound is used. At the identity the dimension is the intended r²−1.
- K=k is included in the extension quantifier, as are inseparable extensions.
  The common universe u is the existing library convention for fields, schemes and
  matrix indices; there is no independent smaller universe on extension fields.
- A group of rational points cannot replace the quotient: for example SL₂(ℝ) → PGL₂(ℝ)
  is not onto, while the stated scheme map is surjective. The formal statement has the
  latter meaning and imposes no surjectivity on rational points.

Searches performed with the required wrapper and source searches:

- `msearch.py ... leansearch "projective general linear group scheme finite faithfully flat
  special linear central cover"`: eight hits on linear groups, abstract special linear
  groups and `Matrix.ProjectiveSpecialLinearGroup`; none is this group-scheme quotient.
- `msearch.py ... leanfinder "PGL group scheme as quotient of GL by scalar matrices"`:
  eight hits, including `Matrix.ProjectiveSpecialLinearGroup`, projective vector-space
  actions and abstract SL; no affine scheme PGL or this central-cover theorem.
- `msearch.py ... loogle "Matrix.GeneralLinearGroup, GrpObj.ker"`: no hits (the service
  reports unknown identifier `GrpObj.ker`, which is project upstream, not Mathlib).
  The actual upstream kernel source was therefore read directly.
- `msearch.py ... grep "PGL|projectiveGeneralLinear|projective.*linear.*group"
  AlgebraicGeometry`: three irrelevant `Gluing.lean` hits, no quotient declaration.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for PGL, projective linear groups,
  central covers and the item id: no theorem matching the item. Existing PGL actions
  in `PGLLinearizedPolarization` and `AffinePGLAction` are encoded via GL actions with
  trivial scalars, not a construction or statement of this quotient. The GL, SL and μr
  modules were found and reused, not duplicated.
- `rg` over `dag/lean_names_upstream.json` and the two source trees for the proposed
  namespace and theorem name: no name collision. Searches for geometric connectedness
  found the existing Mathlib class, which is used directly.

Validation: the delivered module compiled individually through `scompile.py`, in both
its sandbox and library module contexts, cleanly within the 60-second limit. The first
probe exposed an inference issue in the scalar coordinate map, fixed by naming its
source and target algebras explicitly. There are no diagnostic commands, local notation,
local instances, auto-bound implicits, or extra theorem proofs in the delivery.

## Second reading by Q09

Author's separate clause-by-clause rereading; no independent agent was started, as the
dispatcher's brief forbids subagents and assigns independent review to the maintainer.
I reopened the node and final module. The table above checks every hypothesis and
conclusion. In particular I checked that the fpqc sheaf condition is paired with the
universal property, the scalar morphism is tI, q is exactly the restriction of π, the
kernel isomorphism respects j, both torsor isomorphisms have their two actual projection
formulas, and the direct-image rank is not omitted in favor of just fibre degree.
The comparisons under field extension fix every polynomial generator and commute with
all four specified maps; the induced torsor comparisons are therefore determined by
projections. No mathematical clause was changed on rereading. I replaced the literal
positivity proof in `rootsScalar` by the existing named lemma `Nat.zero_lt_two`.
Only `exists_presentation` has `sorry`, with all ten proof steps in its docstring.
