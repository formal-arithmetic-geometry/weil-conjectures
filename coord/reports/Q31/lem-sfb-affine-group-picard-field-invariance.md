## Worker report

Item: `lem-sfb-affine-group-picard-field-invariance`, group Q31, stage 2.

The module `Sheaf.AlgebraicGeometry.AffineGroupPicardFieldInvariance` states
`AlgebraicGeometry.affineGroup_picard_field_invariance`, with its entire proof `sorry`.
It introduces no definitions and proves nothing. Its docstring carries all six steps of
the accepted DAG proof, including the explicit cokernel chase.

The node's statement is unchanged. Two already stated nodes are added to `stmt_deps`:
`def-sc-picard-group` and `lem-sc-pic-group`. They record the existing scheme Picard
classes and tensor group law actually used here. No new notion or dependency repair is needed.

Hypotheses and conclusions match as follows:

| Node clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| k is algebraically closed | `[IsAlgClosed k]` |
| G is a k-scheme with a group structure | `(G : Over (Spec (CommRingCat.of k))) [GrpObj G]` |
| G is smooth over k | `[Smooth G.hom]` |
| G is connected | `[ConnectedSpace G.left]`, including nonemptiness |
| G is affine | `[IsAffine G.left]` |
| G is of finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the recorded finite-type convention |
| Every field extension K/k | `(K : Type u) [Field K] [Algebra k K]` |
| G_K is the fibre product over Spec k | `pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))` |
| p_K is the projection to G | `pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))` |
| Picard classes are isomorphism classes of invertible modules | Existing `Scheme.Pic`, the subtype of invertible classes in the skeleton of `Scheme.Modules` |
| Tensor product is the abelian group law | Existing `Scheme.Pic.instCommGroup` uses multiplication for tensor product, one for the structure sheaf, and inverse for the dual |
| The map is canonical pullback | Existing `Scheme.Pic.mapHom` of the displayed projection; its underlying map is `Scheme.Pic.map`, induced by `Scheme.Modules.pullback` |
| Pullback is an isomorphism of abelian groups | `Function.Bijective (Scheme.Pic.mapHom ...)`; since this is already a group homomorphism, bijectivity is exactly the isomorphism assertion |
| No algebraicity, separability, perfection restriction | None of these is a binder, and there is no `[IsAlgClosed K]` |
| The trivial group is included | No nontriviality, positive-dimension, or nonempty-root-system hypothesis |

The explicitly declared universe `u` is the ambient universe for schemes and both fields,
as in the existing scheme Picard/pullback API. Picard groups themselves live in
`Type (u + 1)`. There are no implicitly auto-bound variables or universes; both
`autoImplicit` and `relaxedAutoImplicit` are disabled.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, for `def-weil-field`.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, the algebraically-closed-field
  component explicitly identified by `def-weil-algebraic-closure.mathlib_match`.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, for
  `def-sc-group-scheme`, on `Over (Spec (.of k))`. Its cartesian interface comes from
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. The existing upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents this specialization.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth, for
  `def-sbc-smooth-morphisms`.
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic, for `def-weil-connected-scheme`.
- `AlgebraicGeometry.Spec` and `Spec.map`, Mathlib.AlgebraicGeometry.Scheme, for
  `def-weil-affine-spectrum`. `IsAffine` is the existing scheme affineness predicate.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, Mathlib morphism modules,
  for `def-weil-finite-type-morphism`.
- `Algebra`, Mathlib.Algebra.Algebra.Defs, for `def-pc-field-extension`.
- `Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible, for `def-sc-invertible-module`.
- `SheafOfModules.cochainModulesMonoidal`,
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, for the recorded
  `def-pur-sheaf-tensor-product` interface. The scheme tensor/Picard constructions
  already use this sheaf tensor notion; it is not redefined.
- `CategoryTheory.Limits.pullback` and `pullback.fst`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, for `def-pc-fibre-product`.
- `Scheme.Modules.tensorPullbackSectionAdjunction`,
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction, for the recorded
  `def-pc-module-pullback` interface. Canonical Picard pullback reuses upstream
  `Scheme.Modules.pullback`; no arbitrary new map is introduced. This existing
  Picard interface acts on isomorphism classes. The tensor pullback and that upstream
  pullback are naturally isomorphic by left-adjoint uniqueness, since the recorded
  `tensorPullbackSectionAdjunction` and `pullbackPushforwardAdjunction` have the same
  right adjoint. Consequently the existing Picard map is exactly tensor pullback on
  classes, without introducing a second Picard map or a second definition of pullback.
- `Scheme.Pic`, WeilConjectures.AlgebraicGeometry.PicardFunctor, for the added
  `def-sc-picard-group` dependency; `Scheme.Pic.instCommGroup` and `Scheme.Pic.mapHom`,
  WeilConjectures.AlgebraicGeometry.Picard.Group, for the added `lem-sc-pic-group`
  dependency and the canonical homomorphism.

All recorded statement dependency modules are publicly imported, directly or through
`Picard.Group`. The stated proof dependency `def-sc-gm-ga` is imported through
`Sheaf.AlgebraicGeometry.StandardGroupSchemes` as a plain proof import. The four
supporting geometric theorem nodes in `proof_deps` have no Lean records in the read
repository at preparation time, so they supply no module imports yet. Their roles remain
in the complete proof docstring; they are proof prerequisites rather than missing
statement notions.

Source check: read Brion, *On Linearization of Line Bundles*,
[the primary publisher PDF](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms220104.pdf),
Remark 2.2(v) and Lemma 2.3, printed pp.117--118. Over an algebraically closed field,
the connected affine group is split. The lemma gives invariance for arbitrary field
extensions. Its proof reduces through the split unipotent quotient to the reductive
case and computes the Picard group from root data. The node takes the invariance
conclusion. The current blueprint direct-image stability proof (3) was also read; this
is a supporting node in its inherited alteration/linearization route.

Edge cases checked mathematically before writing:

- Trivial group: both Picard groups are trivial; all hypotheses allow it.
- Split torus and split unipotent group: Picard groups are zero; no positive rank or
  nonempty Schubert-boundary assumption was introduced.
- Noncommutative reductive group such as PGL2: allowed by `[GrpObj G]` with no
  `[IsCommMonObj G]`; its possibly nonzero finite Picard group is retained.
- Identity extension K = k: the projection is an isomorphism and this is its actual
  Picard pullback, not an arbitrary equivalence between the groups.
- Transcendental and imperfect extensions in positive characteristic: permitted;
  no finite-type, algebraic, separability, or perfection condition is placed on K/k.
- Empty scheme: excluded already by connectedness (and the group identity);
  no additional nonemptiness condition is inserted.

Searches made (all three external interfaces were used through msearch.py):

- LeanFinder: `Picard group pullback of a smooth connected affine group scheme over
  algebraically closed field is bijective after any field extension` returned eight
  hits on cotangent spaces, Galois-category maps, affine points, and affine-space
  surjectivity. None states the result.
- Loogle: `CommRing.Pic.mapAlgebra, AlgebraicGeometry.Scheme.PicardGroup` returned no
  hits (the guessed scheme name is unknown). Follow-up `"Pic", "mapAlgebra"`
  returned seven ring Picard functoriality/exactness declarations, including
  `CommRing.Pic.mapAlgebra`; none proves the required bijectivity.
- LeanSearch: `Picard group of a smooth connected affine algebraic group unchanged by
  scalar extension of an algebraically closed field` returned ring Picard definitions,
  functoriality and local-ring triviality; none states this group-scheme result.
- msearch grep: `Picard|picard|mapAlgebra`, subdirectory `AlgebraicGeometry`, returned
  three elliptic-curve comments, no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Picard, Pic, pullback, affine/field
  combinations found the scheme `Pic`, `Pic.map`, `Pic.mapHom`, and their tensor group
  law. These are reused. Curve-specific torsion/degree-zero results do not state this
  theorem. The exact item id has no upstream declaration hit.
- `rg` in `dag/lean_names_upstream.json` and both library roots for the proposed name
  and field-invariance phrases found no matching declaration. DAG inspection found
  `def-sc-picard-group` and `lem-sc-pic-group`, which are cited instead of making a
  new definition node.

No statement dispute, corrected statement, hollow definition, or unusable dependency
interface was found.

Validation: prescribed scompile.py compiled both its sandbox probe and the actual
library module successfully (30.7 s and 2.2 s respectively), with no error or unexpected
warning. All Lean lines are at most 100 characters. The node signature is copied
verbatim from the theorem header; existing node fields are preserved except `lean` and
the two authorized additions to `stmt_deps`.

## Second reading by Q31

Author's self-reading, not an independent review; the dispatcher forbids starting
other agents, and the maintainer supplies the independent delivery review. Reopened
the node and module and compared every row above: the field, group, smoothness,
connectedness, affineness, finite-type and arbitrary-extension binders agree. The
projection has the correct orientation from G_K to G. The conclusion concerns the
existing canonical group homomorphism, hence includes compatibility with tensor
product and the structure-sheaf identity through its existing type and definition.
The multiplicative notation changes no mathematical object. No assertion of Picard
finiteness was added. No mismatch or correction was needed.
