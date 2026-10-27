## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisConnectedImageInvariantSeparation` states
`AlgebraicGeometry.galois_connected_image_invariant_separation`, with its whole proof
`sorry`. No definitions or auxiliary theorems are introduced. The item node changes only
in `lean`. The source is Stacks `varieties.tex`, Tag 038C, `lemma-tricky`, especially
its first paragraph and intersection/union display; the preceding
`equation-galois-action-base-change-kbar` explains the opposite action. These passages
were read locally, together with the current blueprint locality statement and proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fields and extension are `(k L : Type u) [Field k] [Field L] [Algebra k L]`.
  `[FiniteDimensional k L]` supplies finiteness. `[IsGalois k L]` is precisely separable
  algebraic plus normal: the Mathlib class has `Algebra.IsSeparable` and `Normal` fields,
  and the latter says every minimal polynomial splits. No extra field condition is imposed.
- `(T X : Scheme.{u})` with their `Over (Spec (.of k))` instances gives the two schemes
  over k. `(f : T ⟶ X) [f.IsOver (Spec (.of k))]` gives exactly a morphism over k.
- `T.baseChangeField k L` and `X.baseChangeField k L` unfold to the prescribed pullbacks
  along `Spec.map (CommRingCat.ofHom (algebraMap k L))`.
- `[ConnectedSpace (T.baseChangeField k L)]` includes nonemptiness, exactly as required.
  The range in the conclusion is that of
  `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map
  (f.asOver (Spec (.of k)))).left`, the canonical base change of f; it is not a chosen map.
- `(A B : Set (X.baseChangeField k L))`, `hA`, `hB`, `hAne`, `hBne`, `hdisj`, and
  `hcover` render both nonempty clopen parts, disjointness, and their union being all X_L.
- `∃ C P Q` with `(C = A ∨ C = B)` expresses the possible interchange: C is the part
  called A after relabeling. There is no unrelated clopen set permitted in its place.
- `P = ⋂ σ : L ≃ₐ[k] L, (baseChangeMap ... (specAlgEquivOver σ)) '' C` gives exactly
  the prescribed intersection, indexed by all k-algebra automorphisms of L.
  `specAlgEquivOver σ` has underlying morphism `Spec.map` of σ, without inversion;
  `baseChangeMap` therefore is precisely id_X × Spec(σ), with the opposite composition law.
- `Q = Pᶜ` gives the prescribed complement.
- `P.Nonempty ∧ Q.Nonempty ∧ IsClopen P ∧ IsClopen Q` gives all four assertions.
- `Disjoint P Q ∧ P ∪ Q = Set.univ` gives X_L = P disjoint-union Q.
- `Set.range (...) ⊆ P ∧ P ⊆ C` gives exactly f_L(T_L) ⊆ P ⊆ A after relabeling.
- The final `∀ σ`, with the two image equalities, gives σ_X(P) = P and σ_X(Q) = Q.
- There is no connectedness hypothesis on X or geometric connectedness hypothesis on T.
  The common arbitrary universe is the library's scheme/base-change size convention;
  all individual fields and schemes can be placed in one ambient universe.

Dependency interfaces read and used:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` / `algebraMap`.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`, supplied through `Mathlib.FieldTheory.Galois.Basic.IsGalois`.
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`, `Scheme.Over`,
  `Scheme.Hom.IsOver`, and `Scheme.Hom.asOver`.
- `def-pc-base-change`: public import of the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; the node's own record explains
  that `moduleBaseChange` is only for modules and that schemes/maps use pullback and
  `Over.pullback`. Also use its upstream audit's `Scheme.baseChangeField` from
  `WeilConjectures.AlgebraicGeometry.BaseChangeField`.
- `def-weil-connected-scheme`: `ConnectedSpace` from
  `Mathlib.Topology.Connected.Basic` (publicly available through `Connected.Clopen`),
  whose class includes `Nonempty`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec` / `Spec.map`.
- The recorded base-change construction `AlgebraicGeometry.baseChangeMap` was read in
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`. The canonical spectrum automorphism
  `AlgebraicGeometry.specAlgEquivOver` was read in the publicly imported
  `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`.
- Proof dependencies `def-pc-scheme`, `def-pc-fibre-product` and
  `lem-weil-pbc-finite-galois-fixed-field` are already publicly exposed by these imports:
  `Scheme`, `Scheme.Hom`, `Limits.pullback` and its projections, and the Galois/Fixed
  declarations `AlgEquiv.fintype`, `IsGalois.card_aut_eq_finrank`, and
  `IsGalois.mem_range_algebraMap_iff_fixed`. Their signatures were read.

Edge cases checked before drafting: empty T_L is excluded by ConnectedSpace's nonempty
field; empty X_L cannot have the hypothesized partition. If L = k, the intersection is
the chosen original part. If the image lies in B instead of A, C = B covers that case.
Disconnected X is allowed (e.g. two copies of Spec k, with T mapping into one copy).
No quasi-compactness, quasi-separatedness, characteristic, finite-type or smoothness
hypothesis occurs. The opposite action law affects reindexing but not the definition
of a translate. P contains the nonempty invariant image, and Q contains the opposite
original part, so both nonemptiness claims have their required hypotheses.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: `finite Galois base change connected image invariant clopen separation of
  schemes`: eight hits about stability of finite/separated morphisms under base change,
  proper/finite morphisms, and discrete fibres; no exact match.
- Loogle: `IsClopen, Set.iInter`: seven hits including `isClopen_iInter_of_finite` and
  `Set.Finite.isClopen_biInter`; these supply only the finite-intersection topological step.
- LeanSearch: `Galois invariant clopen separation containing connected image of scheme
  base change`: eight hits on opens Galois insertion, stable morphism properties and
  Krull topology; no matching scheme statement.
- Mathlib grep: `[Gg]alois.*[Cc]lopen|[Cc]lopen.*[Gg]alois|[Ii]nvariant.*[Cc]lopen`:
  zero hits.
- Project/upstream `rg` for the corresponding Galois/clopen and connected-image phrases
  found `GaloisFiniteInvariantClopenPartition`,
  `GeometricallyConnectedFiniteSeparableTest`, and `GeometricallyConnectedImageCriterion`.
  Their statements were read: the first changes the intermediate base and does not give
  the prescribed refinement containing this image; the latter two are geometric
  connectedness criteria, not this lemma. They are not exact matches.
- Literal grep of the item id in `lean/WeilConjectures` had no hits. Search for the proposed
  declaration in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  had no hits. Searches for canonical maps found the existing `specAlgEquivOver` and
  `baseChangeMap`, which are reused without private copies.

The brief's sample Sheaf CompactObject module is withdrawn; its recorded upstream
`WeilConjectures.CategoryTheory.CompactObject` was read instead. No mathematical node
fault, disputed statement, missing notion, or dependency repair was found.

Validation: scompile.py compiled this file individually in both sandbox and final module
contexts, with no errors or unexpected warnings (13.6 s and 9.6 s respectively).

## Second reading by Q81

I reopened the written module and the original node and performed a separate clause-by-clause
reading. This is a single-worker rereading: the dispatcher explicitly prohibits starting
other agents; the maintainer's delivery review provides the independent reading.
The field assumptions match finite Galois exactly. The IsOver instance is essential to
base-change f, and is present. ConnectedSpace is imposed on T_L, not T or X_L, and includes
nonemptiness. All six partition hypotheses are present. C is constrained to one original
part, so the swap is valid, including the case where the image lies in B. P is constrained
to the actual intersection of images under the canonical maps; Q is its complement.
Both nonemptiness and both clopenness conclusions are explicit, as are disjointness and
coverage. The range is that of the Over.pullback map of f and hence exactly f_L(T_L).
P is contained in the selected original part, and the last two equalities quantify over
every automorphism. No stronger geometric or connectedness assumptions were introduced.
The source and all five node proof steps are recorded in the theorem docstring.
No mismatch was found and no statement change was made.
