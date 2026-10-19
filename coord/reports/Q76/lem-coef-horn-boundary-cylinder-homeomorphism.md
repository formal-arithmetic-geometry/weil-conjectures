## Worker report

The module `Sheaf.Topology.HornBoundaryCylinderHomeomorphism` states
`EuclideanGeometry.horn_boundary_cylinder_homeomorphism`. Its sole theorem has
proof `sorry`; no definition or auxiliary theorem is introduced. Only the item's
`lean` field changes.

Clause-by-clause correspondence:

- The integer dimension and lower bound are `(n : ℕ) (hn : 2 ≤ n)`.
- The full index range `0 ≤ i ≤ n` is `(i : Fin (n + 1))`, including both end indices.
- The identified realized simplex is `stdSimplex ℝ (Fin (n + 1))`. Its pinned
  Mathlib definition is exactly nonnegative coordinates with total sum one.
- The opposite face is the literal set
  `{t : Fin (n + 1) → ℝ | t ∈ stdSimplex ℝ (Fin (n + 1)) ∧ t i = 0}`.
  It is used directly, without a second definition of a simplex or a face.
- The cylinder is that face `×ˢ Set.Icc (0 : ℝ) 1`, in the ambient real product
  coordinate space. In particular, the interval includes both endpoints.
- Both requested boundaries are `intrinsicFrontier ℝ` of the corresponding set.
  I read `Mathlib.Analysis.Convex.Intrinsic`: this is the image in the ambient space
  of the frontier of the set in its affine span, exactly the relative frontier.
- Existence of the boundary homeomorphism is `∃ ψ : ... ≃ₜ ...`.
- Inside the domain boundary the horn is
  `{t | ∃ j : Fin (n + 1), j ≠ i ∧ t.val j = 0}`.
  The boundary of the closed simplex is contained in the simplex; conversely any
  simplex point with a zero coordinate is in its relative frontier. Thus this is
  exactly H_i, with no points omitted by using the boundary as the ambient type.
- The final equality says the ambient image of that horn under `t ↦ (ψ t).val`
  is exactly `{p | p.1 ∈ stdSimplex ℝ (Fin (n + 1)) ∧ p.1 i = 0 ∧ p.2 = 0}`,
  namely F_i times {0}. A homeomorphism restricts to a homeomorphism onto the image
  of every subset, so equality with the whole bottom expresses the requested
  restriction homeomorphism. It asserts surjectivity onto the bottom, rather than
  merely containment there. Conversely the node's restriction gives this equality.
- All the coordinate, product, affine-span and boundary subtypes use Mathlib's
  induced topology. The finite real function space's topology is the usual
  Euclidean topology (its standard norm is equivalent to the Euclidean norm).
  Nested induced subspace topologies agree with those induced from the ambient
  coordinate space. No compactly generated replacement topology is introduced.

Dependency declarations read and used:

- `def-kun-subspace-topology`: `instTopologicalSpaceSubtype`,
  `Mathlib.Topology.Defs.Induced`, lines 76–78. Its complete signature is
  `{p : X → Prop} [t : TopologicalSpace X] : TopologicalSpace (Subtype p)` and its
  data is `induced (↑) t`. The mathlib-match record is directly usable.
- The proof dependency `lem-coef-closed-union-continuity` is the Mathlib leaf
  `ContinuousOn.union_of_isClosed`, `Mathlib.Topology.ContinuousOn`, lines 879–887:
  given `ContinuousOn f s`, `ContinuousOn f t`, `IsClosed s`, `IsClosed t`, its
  conclusion is `ContinuousOn f (s ∪ t)`. Its module is imported non-publicly for
  the recorded proof plan. No dependency interface repair is needed.
- Other existing Mathlib objects used are `stdSimplex` from
  `Mathlib.Analysis.Convex.StdSimplex`, `intrinsicFrontier` from
  `Mathlib.Analysis.Convex.Intrinsic`, `Homeomorph` from
  `Mathlib.Topology.Homeomorph.Defs`, and ordinary set product, interval and image.

Edge cases checked before writing: n=2 gives the triangle boundary and rectangle
boundary, with two edges carried to the entire bottom edge; both i=0 and i=n are
allowed. At a vertex the horn condition still uses some j unequal to i, as stated.
Points in H_i intersect F_i satisfy both conditions and remain on the bottom
boundary. The barycentre of F_i is not its relative boundary but (c,0) is on the
cylinder boundary. This distinguishes intrinsic from ambient frontier. The proof's
radial centre r=0 uses the first branch; the seam r=1/2 agrees; r=1 maps to height
zero. Dimensions zero and one are excluded only by the stated n≥2 assumption.
No independent universe variable or extra nonemptiness assumption is introduced.

Searches for an existing statement, performed via the prescribed `msearch.py`:

- LeanFinder: “The boundary of a simplex is homeomorphic to the boundary of the
  opposite face times the unit interval with a horn carried onto the bottom”.
  Eight hits, including `SSet.horn.faceι`, `SSet.face_le_horn`,
  `SSet.boundary_eq_iSup`; these are simplicial inclusions/identities, not the
  required topological boundary homeomorphism.
- Loogle: `stdSimplex, Homeomorph`. Five hits are the one-dimensional
  `stdSimplexHomeomorphUnitInterval` and its evaluation lemmas, not this statement.
- Mathlib grep (Analysis):
  `horn.*[Hh]omeomorph|[Hh]omeomorph.*horn|intrinsicFrontier`.
  Five hits identify the existing relative-frontier notion in Convex/Intrinsic.
- LeanSearch: “A homeomorphism between the boundaries of a simplex and a simplex
  cylinder takes a horn onto the bottom face”. Eight hits: ordinary
  `Homeomorph.image_frontier`, the one-simplex/interval homeomorphism and simplicial
  horn declarations, none stating this boundary-pair homeomorphism.
- `rg` over upstream `WeilConjectures`, its Topology and Mathlib/Topology
  subdirectories, and project `lean/Sheaf`, for horn, stdSimplex,
  intrinsicFrontier and the proposed declaration name; also the mandated
  `grep -rn` for this node id in upstream. No existing declaration states it.
  The project has `EuclideanGeometry.polytope_boundary_radial_extension`, a
  theorem extending an already prescribed polytope boundary homeomorphism; it
  does not supply the horn-to-bottom boundary homeomorphism. The project also has
  `SSet.Enhanced.serreLastHorn` in `SerreDiskLiftBoundaryBijection`, the range of
  the actual realized last-horn inclusion; its source was read. It is on the
  realization object and uses the last horn only, whereas this node explicitly
  identifies barycentric coordinates and allows every i. No copy of it is defined.
- The proposed full declaration name was searched in Mathlib, upstream,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

Source check: I opened Hovey's PDF at the node's URL and read printed p.79
(PDF page 88), the paragraph after Proposition 3.2.2 and before 3.2.3. It asserts
the simplex/disk-cylinder pair identification carrying the horn to the disk end.
The explicit minimum/radial formulas are the agent's expansion in this node's
proof, not formulas printed in Hovey. The inherited `source.place` description
“explicit coning and radial-coordinate construction” overattributes that part to
Hovey; the module distinguishes the source assertion from the recorded agent
proof. This metadata observation does not require a statement change.
Source link: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf

Validation: the prescribed `scompile.py Q76
lem-coef-horn-boundary-cylinder-homeomorphism <module file>` completed successfully
for both the sandbox and library module checks, with no errors or warnings.
All binders are explicit and `autoImplicit` is disabled. The five node proof steps
are included in the theorem docstring. No statement fault or disputed statement.

## Second reading by Q76

This is the author's second pass, not the independent maintainer review. I reopened
the node and the final module and checked the dimension bound, all face indices,
nonnegative sum-one simplex, zero-coordinate horn, opposite face, closed interval,
relative affine-span frontiers, and the homeomorphism's entire horn image against
the signature. I specifically checked that the image is in the ambient product,
so equality names every point of F_i times {0}, and that the restriction is
homeomorphic because ψ is already a homeomorphism and subspaces have the induced
topologies. The horn set is typed inside the simplex boundary, where simplex
membership is automatic; this does not add a hypothesis or discard a horn point.
There are no missing hypotheses or clauses, no new notions, and no dependency
repairs. No edits were required in this second pass. Independent review is left
to the maintainer as specified by the dispatch brief.
