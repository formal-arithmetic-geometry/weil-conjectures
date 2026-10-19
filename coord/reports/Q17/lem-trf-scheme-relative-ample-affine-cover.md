## Worker report

This repair converts the returned stage-1 split into the required stage-2
statement. The module
`lean/Sheaf/TraceFormula/SchemeRelativeAmpleAffineCover.lean` states
`AlgebraicGeometry.scheme_relative_ample_affine_cover`; its proof is exactly
`by sorry`. The node's mathematical statement, source, and proof plan are
unchanged. The module uses the canonical tensor pullback from
`AlgebraicGeometry.Scheme.Modules.tensorPullback`, as required by the project
convention, and supplies its canonical invertibility instance through
`invertible_pullback_tensor`.

The Lean rendering of every hypothesis and clause is:

- `{Z S : Scheme.{u}}` and `h : Z ⟶ S` are the schemes and morphism. The
  instance `[QuasiCompact h]` is precisely the quasi-compactness assumption.
- `N : Z.Modules` with `[N.IsInvertible]` is the invertible `𝒪_Z`-module.
- `{I : Type v}` and `U : I → S.Opens` encode an arbitrary indexed family of
  opens. `hU : ∀ i : I, IsAffineOpen (U i)` says every cover member is affine,
  and `hcover : iSup U = ⊤` says that these opens cover `S`.
- For each `i`, the hypothesis
  `@Scheme.Modules.IsAmple (h ⁻¹ᵁ U i).toScheme
  ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ U i).ι).obj N)
  ((Scheme.Modules.invertible_pullback_tensor (h ⁻¹ᵁ U i).ι).1 N).2`
  states ampleness of the canonical tensor-pullback restriction of `N` to the
  inverse-image open subscheme. The explicit final argument is the canonical
  `IsInvertible` instance produced by the recorded pullback theorem.
- The conclusion quantifies over every `V : S.Opens` and assumes
  `IsAffineOpen V`. It states the same ampleness predicate for the canonical
  restriction to `h ⁻¹ᵁ V`, which is exactly “ample over every affine open of
  the base.”

The statement dependencies and declarations used are:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.QuasiCompact`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`
  from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` from
  `WeilConjectures.AlgebraicGeometry.Ample`.
- `def-pc-module-pullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `lem-weil-pbc-invertible-pullback-tensor`:
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor` from
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.

The proof dependencies named by the node were read from their node records and
are represented in the module imports where a recorded declaration is
available:
`lem-weil-pbc-morphism-affine-schemes-affine`,
`lem-weil-pbc-affine-morphism-permanence`, `def-pc-module-pullback`,
`lem-weil-pbc-pullback-ample-invertible`, and
`lem-weil-pbc-qcqs-morphism-permanence` supply the local affine and
quasi-compact steps; `lem-trf-scheme-ample-canonical-proj-criterion` supplies
the canonical section-algebra criterion; `def-trf-algebraic-space`,
`lem-trf-space-qc-separated-etale-local`, `def-weil-proper-morphism`,
`lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-etale-composition-cancellation`,
`def-weil-closed-immersion`, `def-weil-quasi-separated-morphism`,
`lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`,
`lem-trf-space-section-algebra-etale-base-change`,
`lem-trf-space-line-module-proj-map`,
`lem-weil-pbc-etale-covering-base-change`, and
`lem-trf-space-open-immersion-etale-local` supply the descent and Proj-map
steps. The imported published modules are
`Sheaf.AlgebraicGeometry.AlgebraicSpace`,
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`,
`WeilConjectures.AlgebraicGeometry.AmplePullback`, and the relevant Mathlib
morphism/site modules.

Edge cases checked before writing include a one-member affine cover, the
identity morphism, an empty index type (which cannot satisfy `iSup U = ⊤` on a
nonempty base), and empty schemes. The independent cover universe `v` allows
all index types. Inverse images and tensor pullbacks remain well typed for an
empty inverse image.

Searches for an existing exact declaration were made as follows:

- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q17
  lem-trf-scheme-relative-ample-affine-cover leanfinder "relative ampleness
  checked on an affine open cover"`: returned generic affine-locality APIs
  (`HasAffineProperty.*`) and no relative-ampleness theorem.
- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q17
  lem-trf-scheme-relative-ample-affine-cover loogle "IsAmple"`: zero hits;
  Mathlib has no `IsAmple` declaration.
- `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q17
  lem-trf-scheme-relative-ample-affine-cover grep
  "relative.?ample|IsAmple|ample.*local|local.*ample"`: no matching theorem;
  the hits are unrelated generic locality examples.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for the item id,
  `scheme_relative_ample_affine_cover`, and relative-ampleness patterns found
  no exact declaration. The only relevant existing notions are the absolute
  `Scheme.Modules.IsAmple` and the generic `AmplePullback` theorem.

No statement correction, new node, dependency module, or
`STATEMENT-DISPUTED` finding is needed. The module compiles cleanly with
`scompile.py`; the postponed `sorry` is the only expected proof omission.

## Second reading by Q17

I independently reread the current node and the new module. The theorem has
exactly the node's quasi-compact morphism, invertible module, affine indexed
cover, local ampleness hypotheses, and conclusion for every affine base open.
The inverse-image scheme and canonical tensor pullback are the same objects
used by the project's recorded module-pullback definition. The explicit
invertibility instance only makes the existing `IsAmple` predicate typecheck;
it adds no mathematical hypothesis. The source proof at Stacks Tag 01VJ was
checked against all seven docstring steps: local affine restriction, the
canonical Proj criterion, scheme/algebraic-space locality, descent of
quasi-separatedness, section-algebra comparison, descent of the Proj open
immersion, and the reverse criterion. No mismatch was found and nothing was
changed in the statement beyond the canonical Lean rendering required for
these existing definitions.
