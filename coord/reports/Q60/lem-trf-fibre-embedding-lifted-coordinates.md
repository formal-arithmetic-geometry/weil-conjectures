## Worker report

The module `Sheaf.AlgebraicGeometry.FibreEmbeddingLiftedCoordinates` states
`AlgebraicGeometry.Scheme.Modules.exists_fiber_embedding_lifted_coordinates`.
It has one theorem with proof `sorry`, no new definitions and no dependency repairs.
Only the item's `lean` record changes. No statement correction is needed.

Source read: `literature/stacks-project/coherent.tex`, lemma-ample-in-neighbourhood,
Tag 0D2N, first paragraph, and lemma-ample-on-fibre, Tag 0D2M. The former first
chooses a sufficiently high power with closed-immersion coordinates on the fibre,
then lifts all those coordinates over a common neighbourhood. Choosing a smaller
affine neighbourhood preserves the lifts. The delivered conclusion stops there.

Hypotheses and conclusions, clause by clause:

- Schemes Z and S and the named morphism are `{Z S : Scheme.{u}} (f : Z ⟶ S)`.
  The single explicit universe u is unrestricted.
- Properness is `[IsProper f]`. The Noetherian base is represented by
  `[IsLocallyNoetherian S] [CompactSpace S]`, exactly as specified in the node.
- The invertible module is `(L : Z.Modules) [L.IsInvertible]`.
- The base point is `(s : S)`, and the nonempty scheme-theoretic fibre is
  `[Nonempty (f.fiber s)]`, not an assumption on geometric lifts or rational points.
- The fibre module is `(tensorPullback (f.fiberι s)).obj L`. The hypothesis `hL`
  is the recorded absolute `IsAmple` on precisely that module. Its invertibility
  argument is the conclusion `((invertible_pullback_tensor (f.fiberι s)).1 L).2`;
  no additional invertibility hypothesis is imposed on the fibre.
- `∃ d r : ℕ, 0 < d` means the integers d >= 1 and r >= 0, without an extra
  lower bound on r. The finite coordinate type is `ULift.{u} (Fin (r + 1))`.
  ULift changes only the type's universe and retains exactly r+1 ordered coordinates.
- `∃ U : S.Opens, IsAffineOpen U ∧ ∃ hs : s ∈ U` is an affine open
  neighbourhood of s, with its membership proof used for fibre restriction.
- The family `u` has values in `Γ(L.tensorPow d, f ⁻¹ᵁ U)`. These are exactly
  sections of the restricted tensor power on the inverse-image open Z_U.
- The family `t` has values in the sheaf sections of
  `((tensorPullback (f.fiberι s)).obj L).tensorPow d`. Evaluation
  `(t k).val (op ⊤)` gives its global section on the whole fibre. A compatible
  family of sections on all opens is equivalent to its value on the top open,
  so this representation introduces no additional requirement on the sections.
- The first equality for each k is the actual `tensorPullbackSection` of `u k`
  along `f.fiberι s`, restricted from its inverse-image open to the whole fibre,
  and followed by the recorded `boundaryPullbackPowIso (f.fiberι s) L d`.
  The `homOfLE` is induced by `hs` and the equality
  `(f.fiberHomeo s x).property`; every point of the fibre maps to s.
  Thus t is the prescribed fibre pullback, with the fixed p_j(L,d), not an
  arbitrary scalar multiple or a chosen tensor-power isomorphism.
- `∃ ht : Epi (M.freeHomEquiv.symm t)` for the displayed fibre power M is the
  recorded sheaf-surjectivity definition that the t_k generate that module.
- The existential map `i` has codomain
  `ProjectiveSpace (ULift.{u} (Fin (r + 1))) (Spec (S.residueField s))`.
  Its equality with `ProjectiveSpace.homOfGeneratingSections` fixes it to the
  coordinate morphism of t over `f.fiberToSpecResidueField s`. The explicit
  invertibility proof passed to this constructor is `IsInvertible.tensorPow`
  applied to the already derived invertibility of L_s. The existential name i
  is just a way to state the following clauses for that specified morphism.
- `IsClosedImmersion i` is the requested closed immersion of the fibre.
- `∃ e : (tensorPullback i).obj (ProjectiveSpace.twist ... 1) ≅ M` is the
  twist isomorphism in the stated direction. The final equality for every k
  sends the normalized pullback of `ProjectiveSpace.twistOneSection ... k`
  through `e.hom.app ⊤` to `(t k).val (op ⊤)`. This is quotient compatibility,
  and specifies every coordinate, not just the underlying isomorphism class.
- There is no epimorphism or nonvanishing condition on u over Z_U or away from
  the fibre. No flatness, projectivity of f, or surjectivity of f is assumed.

Dependency declarations read and used (module, name):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff condition).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`
  and `tensorPow`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullbackSection`
  and its normalized section-adjunction interface; the same imported upstream
  `tensorPullback` is used throughout.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, with its `epi` condition expressed directly.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace` (the base-change model).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`, `ProjectiveSpace.twistOneSection`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `Scheme.Modules.invertible_pullback_tensor`.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `Scheme.Modules.boundaryPullbackPowIso`, with its actual recursive construction.
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`:
  `Scheme.Modules.IsInvertible.tensorPow`, needed explicitly in the signature.

The modules for stated proof dependencies are imported without `public`:
`AmpleFibreSectionLifting`, `RelativeProjectiveSpace`, `ProjectiveSpaceFunctorOfPoints`,
`FreeProjectiveBundleBaseChangeSpace` (all under `Sheaf.AlgebraicGeometry`),
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`, and
`Mathlib.AlgebraicGeometry.AffineScheme`. Proper base change, proper-to-separated,
and proper immersion closed use declarations in the already imported Mathlib modules.
`lem-trf-affine-eventual-power-immersion` has no recorded Lean module or Mathlib
match in the read node, so there is no module to import for that proof dependency.
It is not needed to type this statement. The full five-step proof plan is retained
in the theorem docstring, including this dependency.

Edge cases checked before writing:

- d=0 is excluded by `0 < d`, as required; r=0 is allowed and has one coordinate.
- The empty fibre is excluded by the stated nonemptiness hypothesis; the empty
  base has no point s. No extra nonemptiness condition is introduced elsewhere.
- Nonclosed base points are allowed. `fiberHomeo` supplies the point equality
  without assuming that the fibre inclusion is a closed immersion.
- Nonreduced schemes and every residue characteristic are allowed. The base need
  not be affine or separated, and the morphism need not be flat.
- The comparison is defined for arbitrary j and all exponents; its imported
  module name does not impose any square-zero or immersion hypothesis here.

Searches for an existing statement:

1. `msearch.py ... leanfinder` query: "An ample line bundle on a proper fibre has
   projective embedding coordinates lifting to sections on an affine neighbourhood
   of the base point". Eight hits concerned Proj global-section constructions,
   basic opens and homogeneous localization; none states this lifting theorem.
2. `msearch.py ... loogle` query: "IsProper, IsAmple, IsClosedImmersion".
   Zero hits, with diagnostic `loogle: unknown identifier 'IsProper'`; this search
   supplied no positive match and was supplemented by the other searches.
3. `msearch.py ... grep` query:
   `fiber.*[Ee]mbedding|[Ll]ift.*[Cc]oordinates|exists.*[Ff]iber.*[Aa]mple`
   in `AlgebraicGeometry`. Four hits concern the topological embedding `fiberι`
   and discreteness of fibres, not lifting line-bundle coordinates.
4. `rg` with the item id and the same fibre-embedding / lifted-coordinate patterns
   in `lean/WeilConjectures` and `lean/Sheaf` found only unrelated declarations;
   exact declaration-name and title searches found no existing statement.
   `grep -rn` for this node id in `lean/WeilConjectures` returned no match;
   the exact declaration name also has no match in `dag/lean_names_upstream.json`.

Validation: `scompile.py Q60 lem-trf-fibre-embedding-lifted-coordinates <file>`
completed with exit 0. The wrapper's initial local attempt reported
`OSError(28, 'No space left on device')`; its prescribed fallback compiled the
file against current server sources in 5.5 seconds without errors or warnings.
No tool was patched and no live source was changed.

## Second reading by Q60

A separate clause-by-clause reread by the same worker was performed; no second
agent was started, as required by the dispatcher. The maintainer's independent
review remains the independent check. The reread compared the node, the source
paragraph, the dependency signatures and the delivered theorem.

The hypotheses match: proper f, locally Noetherian and quasi-compact S, invertible
L, a point s with nonempty fibre, and absolute ampleness of precisely the tensor
pullback L_s. The conclusion has the positive d, unrestricted r >= 0, affine U
containing s, all r+1 local lifts, and their exact normalized fibre values. The
Epi proof concerns only the fibre sections. The map i is equated to the recorded
coordinate constructor with the fibre structure morphism, so it cannot be an
unrelated closed immersion. The final isomorphism uses the recorded base-change
twist O(1), and its coordinate equations impose quotient compatibility. In
particular a bare `Nonempty (i^*O(1) ≅ M)` would miss a clause and was not used.
No mismatches or statement faults were found; no statement or dependency node
was changed. No STATEMENT-DISPUTED flag is warranted by the source or edge cases.
