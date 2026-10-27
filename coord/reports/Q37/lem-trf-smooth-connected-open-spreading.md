## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedOpenSpreading` states
`AlgebraicGeometry.exists_smooth_geometricallyConnected_fibre_neighbourhood`.
Its single theorem has proof `sorry`, as required for stage 2. There are no new definitions,
new nodes, dependency repairs, or statement changes. The existing general Tag 055W statement
is a proof dependency; it does not already assert the smooth conclusion of this item.

Hypothesis and conclusion correspondence, checked against the node and Stacks
`more-morphisms.tex`, Tag 055W, label `lemma-fibre-geometrically-connected-reduced`, and the
first two proof sentences of Tag 057J (`lemma-normal-morphism-irreducible`):

| Node clause | Lean rendering |
| --- | --- |
| Schemes and smooth morphism h:Y→S | `{Y S : Scheme.{u}} (h : Y ⟶ S) [Smooth h]` |
| h of finite presentation | `[LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]` (all three retained explicitly) |
| A point s in S | `(s : S)` |
| An open subscheme T of Y_s | `(T : (h.fiber s).Opens)` with its canonical open immersion `T.ι` |
| T geometrically connected over κ(s) | `[GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)]` |
| Connectedness includes nonemptiness | Mathlib `GeometricallyConnected` uses `ConnectedSpace`, whose field `toNonempty` excludes the empty space |
| An affine scheme S₁ | existential `(S₁ : Scheme.{u})` and `IsAffine S₁` |
| An étale morphism a:S₁→S | existential `(a : S₁ ⟶ S)` and `Etale a` |
| A point s₁ above s | existential `(s₁ : S₁) (hs : a s₁ = s)` |
| The induced residue-field map is an isomorphism | `IsIso (a.residueFieldMap s₁)`; its domain κ(a(s₁)) is κ(s) by hs |
| A quasi-compact open V in Y×_S S₁ | `∃ V : (pullback h a).Opens, IsCompact (V : Set ↥(pullback h a)) ∧ ...` |
| The composite v is smooth | `Smooth (V.ι ≫ pullback.snd h a)` |
| Every fibre of v is geometrically connected | `GeometricallyConnected (V.ι ≫ pullback.snd h a)`, equivalent to geometric connectedness of every residue-field fibre by `GeometricallyConnected.iff_geometricallyConnected_fiber` |
| V_s₁ equals the specified base change of T as an embedded open | the final equality in `((pullback.snd h a).fiber s₁).Opens`: left side is the inverse image of V under the fibre inclusion; right side is the inverse image of T under the canonical map to h.fiber s |

For the last clause the canonical map is `pullback.map`, using projections to Y, the induced
`Spec.map (a.residueFieldMap s₁)`, and a to map the pullback square to the defining square of
`h.fiber (a s₁)`. Its two compatibility proofs are precisely `pullback.condition` and
`a.SpecMap_residueFieldMap_fromSpecResidueField s₁`, with their orientations reversed.
Composition with `eqToHom (congrArg h.fiber hs)` identifies this target with `h.fiber s`.
The source square is the fibre of the base-changed family. The square over the two residue
fields is cartesian (`isPullback_fiberToSpecResidueField_of_isPullback`), so inverse image of
T is exactly T×_{Spec κ(s)}Spec κ(s₁). Equality of opens in this one ambient scheme is equality
of the corresponding open subschemes, including their restricted structure sheaves. This is
the same canonical encoding as the general spreading theorem's recorded signature.

Dependency declarations read and used (Mathlib modules are prefixed `Mathlib.`):

- `AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms, `Spec`, `Spec.map`.
- `AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`, following the finite
  presentation convention in `def-weil-pbc-scheme-conventions`.
- `CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`.
- `AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Scheme.fromSpecResidueField`, `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`.
- `AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`.
- `AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, via the canonical open inclusions.
- `AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`. This is the connected
  clause of dependency `def-pc-geometrically-irreducible`; its lean.note explicitly directs
  connectedness consumers to this module (the primary recorded Integral module contains the
  other three geometric properties). No replacement of a dependency notion is needed.
- `AlgebraicGeometry.Morphisms.Etale`: `Etale`; `AlgebraicGeometry.AffineScheme`: `IsAffine`;
  `Topology.Connected.Basic`: `ConnectedSpace`, imported through these statement modules.

Proof dependency imports are plain imports. Their declarations are:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`:
  `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`:
  `AlgebraicGeometry.Smooth.geometricallyReduced`.
- `Sheaf.AlgebraicGeometry.Morphisms.GeometricallyConnectedFibreNeighbourhood`:
  `AlgebraicGeometry.exists_geometricallyConnected_fibre_neighbourhood`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, the recorded module of
  `lem-pc-proper-base-change`; only that node's smooth clause is used, supplied by the
  statement import `Mathlib.AlgebraicGeometry.Morphisms.Smooth` through
  `AlgebraicGeometry.smooth_isStableUnderBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` also supplies open immersions being smooth
  and `AlgebraicGeometry.smooth_comp`, the two recorded matches for
  `lem-pc-open-immersion-smooth-composition`.

Edge cases checked before writing: empty T is excluded by geometric connectedness; empty S
has no choice of s; empty Y cannot supply such a T. Disconnected ambient fibres are allowed
and T can be one geometrically connected component. When S is a field point, S₁=S and V=T
are the expected model (a finite-type field fibre is Noetherian, hence this open is
quasi-compact). No irreducibility, properness, separatedness, Noetherian hypothesis on S,
or quasi-compactness of S or T was inserted. Quasi-separatedness of h is retained separately
from quasi-compactness. The universe u is explicit and arbitrary; no independent smaller
field-test universe or restriction on characteristic appears.

Searches performed via `/home/ubuntu/weil-launcher-all/batch2/msearch.py Q37
lem-trf-smooth-connected-open-spreading`:

- leanfinder: `A smooth finitely presented morphism and a geometrically connected open in a
  fibre admit an elementary etale neighbourhood and a quasi-compact open family with
  prescribed fibre and geometrically connected fibres` — 8 hits, on standard smooth charts,
  etale maps and the etale locus; no prescribed-fibre spreading statement.
- loogle: `"Smooth", "GeometricallyConnected"` — 0 hits.
- grep: `geometricallyConnected.*(neighbou?r|spread)|exists.*geometricallyConnected` — 0 hits.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for the
  item id and connected-neighbourhood/spreading names found the general flat/reduced
  spreading theorem and the connected-fibre etale criterion. The former lacks the smooth
  conclusion and the latter is a different criterion. Exact search for the new declaration
  name in those paths and Mathlib found no clash. `grep -rn` for the item id in
  `lean/WeilConjectures` found no existing statement.

Validation: the prescribed `scompile.py` compiled the sandbox and library module cleanly,
1.9 seconds each. Auto-implicit variables are disabled. The only postponed proof is the named
main theorem. No statement dispute or node fault was found.

## Second reading by Q37

A separate checking pass by this same worker, with the node and generated module open;
no second agent was started, as instructed. The maintainer supplies independent review.
I rechecked the smooth and all three finite-presentation binders, the base point, and T as
an open of the actual residue-field fibre. The connectedness hypothesis uses T's structure
map to the correct residue-field spectrum, and its nonemptiness comes from ConnectedSpace.
I checked the four existential objects, the affine/etale/residue-isomorphism assertions,
the quasi-compactness of V itself, and smoothness and geometric connectedness of the same
composite V→S₁. Finally I compared the pullback.map arguments with the general spreading
module line by line: the map starts in the fibre of Y×_S S₁, ends in h.fiber (a s₁), and hs
transports it to h.fiber s before taking the preimage of T. Thus the last clause fixes the
embedded open, rather than merely asserting an abstract isomorphism. Every clause matches;
no changes were required by this pass. No source-based correction or extra hypothesis is
needed. Both the declaration docstring and the node's proof specify the same four steps.
