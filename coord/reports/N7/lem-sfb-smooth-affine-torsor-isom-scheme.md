## Worker report

The new module `Sheaf.AlgebraicGeometry.SmoothAffineTorsorIsomScheme` states
`AlgebraicGeometry.RepresentedRightTorsor.exists_smooth_affine_isomRepresentation`.
Its sole theorem has proof `sorry`. The four helper declarations have real data:
two structures of explicitly specified geometric data and laws, and two graph predicates.
They belong to this node's Isom-functor interface, as permitted by the missing-helper rule;
there is no new independent notion or dependency repair. Only the item's `lean` changes.

Hypothesis and conclusion correspondence:

- Scheme S: `{S : Scheme.{u}}`. Group object H over S:
  `{H : Grp (Over S)}`; this includes multiplication, identity, inversion and group diagrams.
- H smooth and affine: `[Smooth H.X.hom] [IsAffineHom H.X.hom]`.
  There is no field, reductivity, connectedness, commutativity, or Noetherian hypothesis.
- Y an S-scheme: `{Y : Over S}`. The two represented right torsors are
  `(P Q : RepresentedRightTorsor H Y)`, using the recorded dependency verbatim.
  In particular its flatness, surjectivity, locally finite presentation, quasi-compactness,
  quasi-separatedness and cartesian torsor square are retained, with no trivialization assumed.
- For a Y-scheme `T : Over Y`, the T-valued points of P_T on a test S-scheme V,
  over a point `t : V ⟶ T.left`, are exactly the subtype
  `{p : V ⟶ P.space // p ≫ P.projection = t ≫ T.hom}`; likewise for Q_T.
  This is the fibre-product universal property, not a different scheme or an affine-only test.
- `EquivariantIsoAt.app` is a bijection of these fibres for EVERY V and t;
  `naturality` says it is a natural transformation. Yoneda identifies such a family
  uniquely with a T-scheme isomorphism P_T ≅ Q_T. The inverse family is automatically
  natural because the components are equivalences. No scheme map is arbitrarily chosen.
- H_T-points are the maps `h : V ⟶ H.X` together with t. The `equivariance` equation
  uses the actual right actions `P.action` and `Q.action` and Cartesian `lift`.
  Both input points are quantified with their fibre conditions; the implication
  `p' = lift p h ≫ P.action` is not an extra condition on the torsor or action.
  The torsor's cartesian square guarantees the translate is in the same fibre.
- Representability: `R : IsomRepresentation P Q (𝟭 (Over Y))` contains an actual
  `R.space : Over Y` and equivalences `(T ⟶ R.space) ≃ EquivariantIsoAt P Q T`.
  Its naturality uses the graph-defined `IsRestriction`, i.e. actual pullback of
  the same equivariant isomorphism, not arbitrary bijections on the sets of isomorphisms.
- Geometry: `IsAffineHom R.space.hom.left ∧ Smooth R.space.hom.left`;
  the conditional affine-source assertion is `IsAffine Y.left → IsAffine R.space.left.left`.
- Arbitrary base change: `∀ (Z : Over S) (g : Z ⟶ Y)` imposes no flatness condition.
  The restricted functor `T ↦ EquivariantIsoAt P Q ((Over.map g).obj T)` is exactly
  Isom of P_Z and Q_Z under H_Z: all three base-changed fibres at T are P_T, Q_T, H_T.
  `R' : IsomRepresentation P Q (Over.map g)` represents that functor over Z.
  The source of k is the actual pullback `(Over.pullback g).obj R.space`,
  `IsIso k` is asserted, and the displayed equality for every T and a says precisely
  that k represents the canonical base-change identification. The normalization uses
  `(Over.mapPullbackAdj g).homEquiv`, so an unrelated isomorphism cannot satisfy it.
- Sections: specialize `R.equiv` to `T = Over.mk (𝟙 Y)`. Its domain consists exactly
  of sections of I → Y, and its codomain is the natural equivariant isomorphisms
  P → Q on all S-tests over Y, hence the actual right H-torsor isomorphisms by Yoneda.
  This is already contained in the representing equivalence, not merely nonemptiness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.RepresentedRightTorsor` (full structure and action laws read).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and universal property;
  the equivalent pointwise fibre description is used above.
- The existing group-object and Cartesian-monoidal APIs are supplied publicly by
  the recorded torsor module. `Over.pullback`, `Over.map`, and `Over.mapPullbackAdj`
  are the existing Mathlib constructions, not replacement pullbacks or comparisons.

Proof imports follow the accepted seven-step split: `AffineFpqcDescent`
(`Over.DescentDatum.isEffective_of_isAffineHom_fpqc`), `FpqcAffineDescent`
(`isAffineHom_of_fpqc_cover`), and Mathlib's `LocalFlatDescent`, `Proper`, `Limits`.
The remaining proof prerequisites (fpqc coverings/axioms, representable descent,
Yoneda, quasi-compact permanence, affine permanence) are exposed by these imports
or the statement dependencies. The seven steps, including c₁ = b₀₁⁻¹c₀a₀₁,
are transcribed in the theorem docstring. No assertion is proved in this delivery.

Sources read: `literature/stacks-project/examples.tex`, Tag 04AG, lines 3915–3945,
which treats an affine group over an algebraically closed field; the node's accepted
fpqc descent proof supplies its explicit arbitrary-base generalization.
Also opened the author-hosted paper
[Cartan–Iwahori–Matsumoto decompositions](https://sites.math.washington.edu/~jarod/papers/iwahori.pdf),
Section 2, Claim 3, printed page 3: the isomorphism scheme is smooth before lifting
through the nilpotent thickenings. This is a supporting special case, not a source
for imposing a complete DVR or reductivity assumption here.

Edge cases checked before writing: empty S or Y (all fibres and section conditions
retain their categorical meanings); trivial H (I = Y, so I need not be affine unless Y is);
noncommutative H (right-action formula and cocycle order retained); two torsors with
no global isomorphism (the representation need not have a section); arbitrary,
including non-flat and identity, base changes. All schemes and all test schemes use
one arbitrary universe u, and no smaller test universe makes equivariance vacuous.
No finite-type, field, or affine-test restriction has been introduced.

Searches actually performed:

- `msearch.py ... leanfinder "isomorphisms of torsors under a smooth affine group scheme
  are represented by a smooth affine scheme"`: 8 hits about affine-space and affine
  scheme isomorphisms; none about torsor Isom representability.
- `msearch.py ... loogle "Grp, Over, IsAffineHom, Smooth"`: zero hits, diagnostic
  `unknown identifier 'Grp'`; not treated as evidence that the group-object API is absent.
- `msearch.py ... grep 'Torsor|torsor' AlgebraicGeometry`: zero Mathlib hits.
- `rg` for torsors and torsor/isom combinations in `lean/WeilConjectures` and
  `lean/Sheaf`: existing finite/étale and coefficient-sheaf torsors, invertible-module
  Isom torsors, and the recorded general torsor definition; no general smooth affine
  represented-torsor Isom theorem. The node-id grep in `lean/WeilConjectures` had no hits.
- Exact new-name grep in both project roots and `dag/lean_names_upstream.json`:
  no `EquivariantIsoAt`, `IsomRepresentation`, or main theorem declaration.
- Current blueprint torsor/isom search used `literature/blueprint/latest/` only.

Validation: prescribed `scompile.py` passed both sandbox and library checks (2.6s
and 2.4s) without errors or warnings. No statement dispute or correction.

## Second reading by N7

Final rereading by the same dispatched worker; the maintainer supplies the independent
review, as the dispatch brief specifies, and no additional agent was started.
I reread the node and the delivered signatures. In particular, I checked that the
base-change representation uses `Over.map g`, not `Over.pullback g` on test schemes:
postcomposition gives the identical P_T, Q_T and H_T over T. Pullback is used only
for the representing scheme. The canonical-map equation has the inverse of the
adjunction equivalence in the correct direction, from a map into I_Z to its underlying
map into I. The graph restriction does not identify merely isomorphism classes:
its variables retain p, q and t, so the actual isomorphism is fixed. Smoothness is
on I → Y, not on the absolute I. The conditional affine clause retains non-affine Y.
The terminal-test specialization gives the full bijection of sections, not just an
existence assertion. All five statement dependencies are usable with their recorded
interfaces; no duplicate torsor definition was supplied. No mathematical mismatch
was found or silently repaired; no node fields outside `lean` were changed.
