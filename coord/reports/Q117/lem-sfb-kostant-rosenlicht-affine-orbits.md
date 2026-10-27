## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.KostantRosenlichtAffineOrbits` states
`AlgebraicGeometry.kostant_rosenlicht_affine_orbits`, with one postponed proof and no
new definitions. The node's statement, dependencies and proof are unchanged.
I read Milne's Theorem 17.64 and proof, printed pp.373--374, from the local PDF with
pdftotext. Section 17h assumes the field algebraically closed; the theorem explicitly
allows an affine algebraic scheme. The docstring carries all five DAG proof steps.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group scheme over k is `V : Grp (Over (Spec (.of k)))`. The bundled group
  has the recorded `GrpObj` structure on `V.X`, with multiplication, identity,
  inverse and their laws. No commutativity is assumed.
- Smoothness, connectedness and affineness are `[Smooth V.X.hom]`,
  `[ConnectedSpace V.X.left]` and `[IsAffine V.X.left]`.
- Finite type of V is `[LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]`.
- Unipotence is exactly `hV : SolvableGroupStructure.IsUnipotent V`, from the
  recorded dependency. I read its full definition: smoothness and a closed faithful
  representation into GL_n, with a positive nilpotence exponent for each point
  over each algebraically closed extension field. Its repeated smoothness is the
  dependency's interface, and imposes no additional hypothesis here.
- The affine finite-type k-scheme Y is `Y : Over (Spec (.of k)))`, with
  `[IsAffine Y.left] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`.
- The action is `[ModObj V.X Y]`. Mathlib's `ModObj.smul` is the morphism
  `V.X ⊗ Y ⟶ Y`; in the Cartesian monoidal over category the tensor is the fibre
  product over Spec k. Its `one_smul` and `mul_smul` fields are precisely the unit
  and multiplication identities. This existing interface is also used by the
  recorded smooth-group-orbit-geometry dependency.
- A rational point is `y : 𝟙_ (Over (Spec (.of k))) ⟶ Y`: the Cartesian tensor
  unit is Spec k over itself, so these are k-morphisms from Spec k.
- The orbit morphism is `lift (𝟙 V.X) (toUnit V.X ≫ y) ≫ γ[V.X, Y]`.
  The two components are identity on V and the constant y map. Its `.left` is the
  underlying scheme morphism, and `Set.range` takes all its topological points,
  rather than just the rational-point orbit.
- Closedness of that image is the first `IsClosed (Set.range ...)` conjunct.
- The reduced induced closed subscheme clause is
  `∃ (O : Scheme.{u}) (j : O ⟶ Y.left), IsReduced O ∧ IsClosedImmersion j ∧
  Set.range j = Set.range ...`. A reduced closed immersion with this exact image
  is the reduced induced structure, uniquely up to the unique isomorphism over Y,
  by the recorded reduced-induced-closed-subscheme theorem. The statement claims
  exactly existence of that structure, and introduces no arbitrary extra data or
  orbit-map flatness conclusion.
- There is no `[IsReduced Y.left]` and no characteristic binder. Thus nilpotents
  and all characteristics are retained. A single explicit arbitrary universe u
  contains k and its schemes; there is no independently smaller test universe.

Recorded dependency declarations used/read:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  and its specialization/documentation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (def-sc-group-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, with `AlgebraicGeometry.QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (finite type).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (including nonemptiness).
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsUnipotent`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `Scheme.IdealSheafData.subscheme`, `subschemeι`, with the nilradical from
  `IdealSheaf.Basic` (def-weil-pbc-scheme-reduction). A reduced closed scheme on
  the image expresses this notion through its intrinsic characterization; no
  private reduction construction is introduced.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod` / `Monoidal.Mod`:
  `CategoryTheory.ModObj`, `ModObj.smul`, `one_smul`, `mul_smul`.
- Plain proof imports include the recorded
  `Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry`
  (`AlgebraicGeometry.exists_smooth_group_orbit_geometry`),
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
  (`AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`),
  and `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`
  (`AlgebraicGeometry.RationalRepresentation.dictionary` and `finite_dictionary`).
  Their full signatures and docstrings were read. Mathlib proof imports provide
  affine-source separatedness, tensor pushout/maps, vector-space freeness,
  Jacobson spaces for finite-type morphisms, and closed-point residue fields.
  The comodule finite-subrepresentation and unipotent fixed-vector nodes have
  neither a Lean record nor a Mathlib match at the time of reading, so they have
  no module to import yet; they are only proof dependencies, not missing notions
  for the present statement.

Edge cases checked before writing:

- Empty Y: there is no rational-point binder inhabitant, so the universal claim
  is vacuous, as the node requires.
- Trivial V: each orbit is the rational closed point; its reduced structure is
  Spec k. Rank-zero faithful representations in the existing unipotence predicate
  are therefore harmless.
- Nonreduced Y, for example Spec k[epsilon]/epsilon^2 with trivial action: the
  underlying orbit is its closed point, and its reduced induced structure is
  Spec k, not the original nonreduced scheme.
- Additive translations of affine space give full affine-line orbits; they include
  generic topological points, which the range of the scheme orbit map retains.
- Positive characteristic and characteristic zero use identical binders.
- The boundary-empty case is already complete in the natural-language proof;
  otherwise the nonzero scalar in the proper ideal yields the contradiction.

Searches for an existing statement (all through the prescribed msearch.py wrapper):

- leanfinder: `Every orbit of a smooth connected unipotent algebraic group acting
  on an affine finite type scheme over an algebraically closed field is closed`.
  Eight hits: autEmbedding_range_isClosed, isClosedMap_smul, pretransitive T1 and
  proper-action/closure lemmas; none is the algebraic-group theorem.
- leansearch: `Kostant Rosenlicht theorem unipotent group orbits on affine schemes
  are closed`. Eight hits: integral/universally-closed morphisms, affine basic-open
  descriptions and closed singleton criteria; no unipotent orbit theorem.
- loogle: `"IsUnipotent", "IsClosed"`. Zero hits.
- grep: `Rosenlicht|Kostant|unipotent.*orbit|orbit.*unipotent`. Two Mathlib hits,
  both differential-algebra citations to Rosenlicht, unrelated to group actions.
- rg in project `lean/WeilConjectures` and `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: searched Rosenlicht/Kostant, IsUnipotent,
  orbit/action interfaces and the exact node id. No existing theorem found;
  found the existing unipotence definition and the orbit-geometry action interface.

No statement correction, new node, dependency repair, or mathematical dispute is needed.

## Second reading by Q117

Final in-thread reading, with the node, source text, dependency definitions and Lean
file open; the maintainer supplies the independent review after delivery. No other
agent was started, as required by this dispatch.

The field, smooth connected affine finite-type V, its exact recorded unipotence
condition, affine finite-type Y, both action laws, and every rational point are
present. The orbit expression agrees verbatim in shape with the one in the recorded
smooth-group-orbit-geometry theorem. Both conclusions refer to its full scheme-point
image. Reducedness is required only of the resulting closed subscheme, with exactly
the prescribed range; this is the uniqueness characterization of the reduced induced
structure, not a choice of a different orbit. No separatedness, reducedness or
characteristic restriction was added to Y. No mismatches found and no changes to the
DAG statement or dependency records were made. All variables and universes are explicit.
