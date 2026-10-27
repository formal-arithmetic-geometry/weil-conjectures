## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperGlobalAlgebraComponents` states
`AlgebraicGeometry.AlgebraicSpace.proper_global_algebra_components`, with one whole-proof
`sorry` and no new definitions. The node's statement, dependencies and proof are unchanged.
I read Stacks `spaces-over-fields.tex`, label
`lemma-proper-geometrically-reduced-global-sections`, Tag 0DMY, clauses (1)--(3) and their
proof. In particular the reduced assertion is ordinary reducedness, not geometric
reducedness, and the algebraically closed conclusion stays inside the reduced clause.

Hypothesis and clause correspondence:

- A field k is `(k : Type u) [Field k]`. The arbitrary algebraic space is
  `X : AlgebraicSpace (Spec (.of k))`. Its structure morphism is `p` to the representable
  base `schemeSpace (Over.mk (𝟙 _))`, and properness is exactly `hp : MapIsProper p`.
  This representable target is terminal among spaces over Spec k: introducing `p`
  does not restrict X or choose an additional map to another base.
- A = Gamma(X_et,O_X) is specified by `A : CommAlgCat.{u} k`, the cone `π` on
  `X.etaleForget.op ⋙ Scheme.Γ`, and `hA : IsLimit (Cone.mk _ π)`.
  This diagram is literally the commutative regular-functions version of the recorded
  `structurePresheaf`; its limit is the ring of compatible global sections, including
  when the site has no terminal chart. `hscalar` pins its k-algebra structure to
  pullback along each chart's structure morphism using `Scheme.ΓSpecIso`.
  These are presentations of the object A named in the node, not extra geometric
  or finiteness hypotheses. A small ring presentation is available for a proper space
  by a finite affine etale atlas and its descent equalizer. Neither chart objects nor
  component indices are forced to live in universe u: they retain universe u+1.
- The component set C is `ConnectedComponents (Point X.obj.obj)` with the recorded
  `pointTopologicalSpace` instance. Mathlib's quotient identifies points precisely
  when their connected components agree; the fibre `ConnectedComponents.mk ⁻¹' {c}`
  is precisely the corresponding maximal nonempty connected subset. It introduces
  no extra empty component. `Finite ...` asserts finiteness, and the following
  universally quantified `IsClopen` asserts openness and closedness of each component.
- Its open-subspace structure is `U c : OpenSubspace X`. The algebraic space `Z c`,
  inclusion `i c`, and presheaf isomorphism `j` identify that space, over X, with
  the very subfunctor U c. The equality of `pointImage (U c).val.ι` with the fibre
  fixes the component. `hi` exposes the representable etaleness needed to form the
  existing `etaleMap` restriction functor. Open representability in `U c` is retained.
- Each factor `B c : CommAlgCat.{u} k` is Gamma((Z c)_et,O_(Z c)), specified by
  the cone `ρ c` and its `IsLimit`. The equivalence `e : A ≃ₐ[k] (∀ c, B c)`
  is the required k-algebra isomorphism. Its chart equation says exactly that the
  c-coordinate is restriction, by evaluating π on `etaleMap (i c) (hi c)`.
  Thus neither the product map nor the factors are arbitrary abstract rings.
  Since e preserves scalars, the same chart equation also pins the scalar map of
  B c to the canonical constants on its charts.
- `Module.Finite k A` is finite dimension over the field. For every c,
  `Nontrivial (B c)`, `IsLocalRing (B c)`, `IsArtinianRing (B c)` express the
  nonzero local Artinian factor, and `Module.Finite k (B c)` its finite dimension.
  IsLocalRing is Mathlib's unique-maximal-ideal convention, and IsArtinianRing is
  the descending-chain condition on ideals (the submodules of the ring over itself).
- Reducedness is `∀ T : X.EtaleSite, AlgebraicGeometry.IsReduced (X.etaleForget.obj T)`.
  This is equivalent to the node's reduced affine etale chart rings: cover every
  etale chart by affine opens, and conversely an affine chart is such an object.
  Under this hypothesis the conclusion is `∀ c, IsField (B c)`; combined with the
  existing canonical k-algebra structure and finite dimension these are precisely
  finite field extensions, including inseparable extensions over imperfect k.
- Under the further `IsAlgClosed k`, `constants` is an equivalence `k^C ≃ₐ[k] A`.
  Its normalization `e (constants a) c = algebraMap k (B c) (a c)` fixes precisely
  the componentwise-constant homomorphism specified in the node. The final equality
  `Module.finrank k A = Nat.card C` is the dimension assertion without choosing a Fintype.
- No Nonempty instance for X or C occurs. The explicit implication from `IsEmpty`
  of the point space to `Subsingleton A` renders A=0 in the empty case. Mathlib's
  connected-component quotient is empty in that case; `∀ c, B c` is the empty
  product and its standard commutative ring is the zero ring. All factor clauses
  are vacuous, and Nat.card C and finrank are zero.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleForget`, `structurePresheaf`, `structureSheaf`, `IsEtale`, `etaleMap`.
  The complete signatures and source docstrings were read; the chart structure
  diagram above is `etaleForget.op ⋙ Scheme.Γ` before forgetting to RingCat.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper` is
  exactly separated, finite type and universally closed, using the recorded chart
  tests and point map, not scheme-only properness.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`; its underlying Point and schemePointMap were read in PointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` is literally
  a subfunctor with representable open-immersion inclusion. No copy is introduced.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: the published `schemeSpace`
  realizes the representable base. This is supporting existing interface data.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`; `GammaSpecAdjunction`
  supplies `Scheme.ΓSpecIso`. `Field` and `IsAlgClosed` are the recorded Mathlib
  notions for the field and algebraic-closure dependencies (only closedness is used).
- Proof-only imports retain the stated proof dependencies: SpaceGradedCohomologyFinite,
  AlgebraicSpaceQuasiCoherentModule, SiteCoveringAxioms, the upstream LocalRing.Basic
  and Artinian.Ring modules. Mathlib Artinian.Ring, Prime.Noetherian, Prime.Topology
  and Localization.AtPrime.Basic provide the recorded Artinian/residue/product leaves.
  `lem-sfb-space-global-idempotent-clopen` has no recorded module at the read base,
  so there is no module to import yet. Its use is preserved in the proof docstring.

Searches actually run:

- msearch leanfinder: `Global sections of a proper algebraic space over a field decompose
  by connected components into finite dimensional local Artinian algebras` returned
  eight scheme/Artinian hits, including `finite_appTop_of_universallyClosed` and
  `isField_of_universallyClosed` for integral schemes. None states this space theorem.
- msearch loogle: `"IsArtinianRing", "IsLocalRing"` returned
  `IsArtinianRing.isField_of_isReduced_of_isLocalRing` and the local maximal-ideal
  quotient-power lemma. These are algebraic ingredients, not the item.
- msearch grep in AlgebraicGeometry:
  `global.*[Ss]ection.*component|[Pp]roper.*[Gg]lobal|ConnectedComponents` returned
  eight scheme-connectedness/constant-sheaf hits; no space theorem.
- rg of WeilConjectures and Sheaf for global sections/functions, component, reduced,
  proper and sectionsSubring located SpaceProperFieldGlobalFunctions (geometrically
  reduced connected case), SpaceH1AffineBaseChange (limit-cone global-ring model),
  and ProperReducedGlobalSectionsProduct (schemes only), all different statements.
  Searching the item id in WeilConjectures returned no occurrence. The upstream
  name index search for global-algebra/component combinations returned no match.
- Read Mathlib's Connected/Clopen definitions of ConnectedComponents and mk and
  Connected/Basic maximality lemmas; no new component notion is necessary.

Edge cases checked: empty space/zero ring/empty product; Spec k; Spec L for a finite
inseparable extension L/k; a connected proper reduced positive-dimensional space
(e.g. P1); Spec k[epsilon]/epsilon^2 (local Artinian, not a field); its disjoint union
with Spec k; reduced disconnected spaces over algebraically closed k. In particular
neither reducedness nor algebraic closedness is assumed in the first product clause,
and algebraic closedness alone does not activate the final clause for a thickening.
No statement fault, correction, disputed statement, new node or dependency repair.

Validation: prescribed scompile.py compiled the module in sandbox and library module
mode cleanly. The only postponed declaration is the named theorem above. No theorem
has been proved; its docstring follows all seven DAG proof steps.

## Second reading by NP

(Written by the maintainer's reviewer, because the delivered section said only that no second
reading had been done (H11). The Lean and the records are unchanged.)

Node clauses against the Lean of `proper_global_algebra_components`, checked against Stacks
spaces-over-fields.tex l.2429-2469 (0DMY (1)-(3) and the proof of (2)):

- Field k: `(k : Type u) [Field k]` (def-weil-field = Mathlib `Field`). OK.
- X an algebraic space over Spec k: `X : AlgebraicSpace (Spec (.of k))`
  (def-trf-algebraic-space, def-weil-affine-spectrum). OK.
- The structure map is proper: `p : X ⟶ schemeSpace (Over.mk (𝟙 _))` with `hp : MapIsProper p`.
  `schemeSpace (Over.mk 𝟙)` is the Yoneda sheaf of S over S, so it is terminal and p is unique.
  This adds no hypothesis. MapIsProper = separated ∧ finite type ∧ universally closed
  (def-sfb-space-morphism-properties). OK.
- |X| with the atlas topology, and C = its connected components:
  `ConnectedComponents (Point X.obj.obj)` with `pointTopologicalSpace`
  (def-a1-space-point-topology). The fibres of `mk` are exactly the maximal nonempty connected
  subsets. OK.
- A = Γ(X_et, O_X): A is given by a limit cone `π`/`hA` over `X.etaleForget.op ⋙ Scheme.Γ`, the
  commutative form of `structurePresheaf`. `hscalar` pins the k-algebra structure through
  `ΓSpecIso` and each chart's structure map. A small model exists because A is
  finite-dimensional, so the theorem is not vacuous. OK.
- C finite; each component clopen: `Finite C`, `IsClopen (mk ⁻¹' {c})`. OK.
- Open-subspace structure: `U c : OpenSubspace X` (def-a1-space-open-subspace). `Z c`, `i c` and
  `j` identify an algebraic space with that subfunctor over X, and
  `pointImage (U c).val.ι = mk ⁻¹' {c}`. Open immersions are étale, so `hi` is true. OK.
- Restriction isomorphism of k-algebras: `e : A ≃ₐ[k] Π c, B c`. Each `B c` is pinned by the
  limit cone `ρ c` on Z c's étale site. The chart equation pins `e` as restriction along
  `etaleMap (i c)`. Since e is a k-algebra map, the k-algebra structure of B c is the canonical
  one. Nothing in the clause is chosen arbitrarily. OK.
- A finite-dimensional: `Module.Finite k A`. Each factor nonzero local Artinian (and finite):
  `Nontrivial ∧ IsLocalRing ∧ IsArtinianRing ∧ Module.Finite k`. OK.
- Reduced (affine étale chart rings reduced): `∀ T, IsReduced (X.etaleForget.obj T)`. This is
  equivalent: affine charts are site objects, and reducedness is affine-local. It is plain
  reducedness, not geometric reducedness, as in 0DMY(3). Conclusion `IsField (B c)`; with
  Module.Finite this is a finite extension. OK.
- k algebraically closed (inside the reduced clause, as in the node): `constants : (C → k) ≃ₐ[k] A`
  pinned by `e (constants a) c = algebraMap k (B c) (a c)`, and `finrank k A = Nat.card C`. OK.
- Empty space: `IsEmpty (Point _) → Subsingleton A`. C is then empty, the product is the zero
  ring, and finrank = Nat.card = 0. No Nonempty assumption. OK.

Edge cases: empty X; Spec k; Spec k[ε] (local Artinian, not a field; the reduced clause is not
active); Spec k ⊔ Spec k; Spec L for an inseparable L/k (reduced, a field, not separable; clause 4
is not claimed); P^1 (connected, A = k). All are consistent with the Lean.

Records: the `lean.statement` is verbatim with the file (whitespace-normalized compare). stmt_deps,
proof and blueprint are unchanged. No new nodes and no dependency modules. All lines are at most
100 characters. The proof is one `sorry`. The docstrings carry 0DMY/0E1E, `(blueprint: …)` and
all seven proof steps.

Advisory, not a fault: `schemeSpace` is owned by def-trf-scheme-algebraic-space, which is not in
the item's stmt_deps. An S2 delivery may not add existing nodes, so it stays a maintainer note
(the same as earlier accepted items). `Point` is reached through def-a1-space-point-topology.

Searches: the worker's leanfinder/loogle/leansearch/grep searches were re-read. The project has
SpaceProperFieldGlobalFunctions (geometrically reduced connected case) and
ProperReducedGlobalSectionsProduct (schemes). Neither is this statement, so there is no H4.
