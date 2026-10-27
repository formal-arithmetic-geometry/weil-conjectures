## Worker report

The delivery states `AlgebraicGeometry.exists_nonempty_separating_pair_open` in
`Sheaf.AlgebraicGeometry.SeparatingPairOpen`. Its proof is `sorry`; no theorem is proved.
The module contains three actual constructions belonging to this statement:
`normPencilTranslateBaseChangeIso`, `normPencilCoordinateSection`, and `normPencilSections`.
None contains postponed data. The first recursively tensors the canonical pullback
composition comparisons of the commuting action squares. The second specializes the
basis sections with the affine coordinate functions. The third computes the existing
norm for the base-changed action and transports it into the actual pullback `B_E^n`.

The independent return on immutable head `073392621d9f` identified an H2 ownership
fault: the statement cited the theorem node `lem-sfb-ample-curve-two-section-pencil`
only for plain definitions in its module. The repair creates the definition node
`def-sfb-pencil-orbit-bundle-norm`, with `existing: true`, owning the seven published
orbit-bundle/norm definitions. The item cites that definition node in place of the
theorem node. The module import remains the recorded module of the new definition owner;
no definition is copied or renamed. The complete Lean file is retained byte for byte.
Compared with current main, the item changes only `lean` and `stmt_deps`; the statement,
proof plan, and proof dependencies retain the already reviewed version.

Clause-by-clause reading:

- The field is `{F : Type u} [Field F]`. The specified F-scheme is `C : Scheme.{u}` with
  `[C.Over (Spec (.of F))]`; every occurrence of its structural map is `C ↘ Spec (.of F)`.
- Smoothness is `[Smooth ...]`; projectivity is `[IsHProjective ...]`, precisely the
  blueprint's finite projective-space embedding convention, rather than a properness
  replacement. Finite type is the two classes `[LocallyOfFiniteType ...]` and
  `[QuasiCompact ...]`. Geometric integrality is `[GeometricallyIntegral ...]`, and
  integrality is `[IsIntegral C]`. Dimension one is `hdim : topologicalKrullDim C = 1`.
- A finite group is `(G : Type v) [Group G] [Fintype G]`. Choosing a finite enumeration
  adds no restriction to a finite group; the group universe remains independent of the
  scheme universe. The action is `ρ : G →* Aut (Over.mk (C ↘ Spec (.of F)))`, so its
  automorphisms are required to be over F, and `Function.Injective ρ` is faithfulness.
- The ample invertible module is `L : C.Modules`, `[L.IsInvertible]`, and `IsAmple C L`.
  The fixed B is exactly `pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L`.
  This is the landed tensor of the translates, not a norm along a quotient map.
- The bound is `∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ...`. Thus it applies to every
  sufficiently large integer n, not just a divisible subsequence or one selected n.
- The finite-dimensional V_n is `((L.tensorPow n).H 0)`, with
  `FiniteDimensional F ...` asserted. `H.zeroLinearEquiv` identifies its basis sections
  with the global sections `Γ(L.tensorPow n, ⊤)`. The F-action on H^0 is the upstream
  restriction of the global-function action along the structure morphism, so this is
  the same F-vector space, not a different cohomology group or assumed finite space.
- For every finite coordinate type I and basis `Module.Basis I F ...`, the parameter
  scheme is `𝔸(I × ULift (Fin 2); Spec (.of F))`. Its two copies of I describe exactly
  V_n × V_n. The universal quantification over bases renders the 'after any choice of
  basis' convention. The open W is a scheme open, with `(W : Set ...).Nonempty`.
- Every extension is `(E : Type u) [Field E] [Algebra F E]`. An E-point is a morphism
  `z : Spec (.of E) ⟶ 𝔸(...)` whose structural composite is
  `Spec.map (CommRingCat.ofHom (algebraMap F E))`. `Set.range z ⊆ W` says that this
  morphism factors through W, equivalently that it belongs to W(E).
- C_E is the categorical pullback of the structural map and Spec E → Spec F. The
  projection `pullback.fst` is used to pull back L and B; `pullback.snd` is the E-map.
  The E-action is the image of ρ under `Over.pullback`, with the underlying morphism
  obtained by forgetting `Over`. This is the actual base-changed action.
- `normPencilCoordinateSection` computes each a or b as the sum of its specialized
  scalar coordinates times the pulled-back basis sections, then applies the existing
  `boundaryPullbackPowIso` to place it in L_E^n. There is no arbitrary map, choice of
  a base-change vector-space identification, or extra section parameter.
- `normPencilSections` uses `pencilNormSection` on these sections and the E-action.
  `normPencilTranslateBaseChangeIso` and `boundaryTensorPowIso` then put both sections
  in the literal `((tensorPullback projection).obj B).tensorPow n`, as the node asks.
- `∃ hB : ... .IsInvertible` exposes the intrinsic invertibility proof needed by the
  coordinate-map API; it is a conclusion, not an additional input. `∃ hs : Epi
  ((SheafOfModules.freeHomEquiv _).symm (normPencilSections ...))` is precisely that
  the two norm sections generate B_E^n.
- The map is the dependency's `ProjectiveSpace.homOfGeneratingSections`, applied to
  the two-entry norm family and `hs`, with target `ℙ(ULift (Fin 2); Spec E) = P^1_E`.
  `IsFinite` and `Surjective` give its two stated properties. The equality for every
  g is `g_E ≫ map = map`, as scheme morphisms, not just on geometric points.
- The final `∃ U : C_E.Opens, Nonempty U ∧ Etale (U.ι ≫ map)` is etaleness on a
  nonempty source open. No global etaleness is asserted.
- W is nonempty as an F-scheme; there is no F-rational-point assertion. No characteristic
  restriction, coprimality, infinite-field hypothesis, or separability condition on E/F
  appears anywhere in the signature.

Dependency interfaces read and used (module; declaration):

- Mathlib.Algebra.Field.Defs; `Field`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective; `IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact;
  `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib.Topology.KrullDimension; `topologicalKrullDim`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible; `Scheme.Modules.IsInvertible`,
  `tensorPow`, `tensorPowTensorObjIso`.
- WeilConjectures.AlgebraicGeometry.Ample; `Scheme.Modules.IsAmple`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, by its public imports;
  the recorded sheafified module tensor, specialized to the scheme's existing monoidal
  module category. The actual section tensor is the existing `tmulSection`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction;
  `tensorPullback`, `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators;
  `SheafOfModules.GeneratingSections` and its defining Epi/freeHomEquiv convention.
- Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections;
  `ProjectiveSpace.homOfGeneratingSections` (full signature and docstring read).
- Mathlib.AlgebraicGeometry.Morphisms.Finite; `IsFinite`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth; `Smooth`.
- Mathlib.AlgebraicGeometry.Geometrically.Integral; `GeometricallyIntegral`.
- Mathlib.AlgebraicGeometry.Properties; `IsIntegral`.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap; `Surjective`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale; `Etale`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
  `baseChange_morphism_projections`, with the stated categorical pullbacks and
  the `Over.pullback` functor. Module base change uses the same tensor pullback.
- Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil;
  `pencilGroupElements`, `pencilTranslateTensor`, `pencilOrbitBundle`,
  `pencilTranslatePowerIso`, `pencilTranslateSection`, `pencilNormSection`.
  Also `pencilUnitPowerIso` supplies the empty-list comparison. These seven plain
  definitions are now owned by `def-sfb-pencil-orbit-bundle-norm` with `existing: true`.
  Read their complete signatures, bodies and docstrings, including the server source
  through `scompile.py --source`. No theorem witness determines these objects.
- WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons;
  `boundaryPullbackTensorIso`, `boundaryTensorPowIso`, `boundaryPullbackPowIso`,
  and `boundaryPullbackComparison`, canonically determined by tensor pullback.
- WeilConjectures.AlgebraicGeometry.Cohomology.Defs;
  `Scheme.Modules.H`, `H.zeroLinearEquiv`, `moduleHOfField`, `globalSectionsRingHom`.

All recorded proof-dependency modules that have statements are imported without public
visibility. For Mathlib leaves, the corresponding existing modules are imported. The
function-field module landed while this worker was running and is used by its recorded
module name. No theorem from the parent invariant-local-pencil node is imported, avoiding
an import cycle.

Source checks: read coherent.tex `lemma-kill-by-twisting` (02O1), including its four
proper/Noetherian/coherent/ample hypotheses and the proof; read curves.tex
`lemma-generically-etale` (0C1C), all five equivalent clauses and its proof. The norm
parameter-space argument and all seventeen DAG proof steps are transcribed into the
main theorem docstring. The construction is the reviewed original-curve norm replacement
recorded by the node, not a quotient curve or an averaging argument.

Edge cases checked: G trivial; characteristic dividing |G| (one simple-zero factor,
without averaging); finite F (W(F) can be empty); E = F and inseparable extensions;
empty coordinate index (a basis of a zero-dimensional section space, not excluded by
an artificial Nonempty binder); exponent zero in the canonical comparisons; and the
empty scheme, which is already excluded by the node's integral, dimension-one assumptions.
The field and scheme universe is u in all base changes, as in the recorded Mathlib
geometric-integrality convention; the finite group has its own universe v.

Searches for existing declarations:

1. `msearch.py ... leanfinder` query: nonempty Zariski open of pairs of sections whose
   group norms define a finite generically etale invariant curve pencil. Eight hits,
   on etale loci, standard smooth maps and elliptic-curve normal forms; no theorem match.
2. `msearch.py ... loogle` query: AlgebraicGeometry.Scheme.Modules, IsAmple, AffineSpace.
   Output: `[loogle] OK 0 hit(s) | loogle: unknown identifier 'IsAmple'`.
3. `msearch.py ... grep` query: norm.*[Ss]ection|[Nn]orm[Pp]encil|separating.*[Ss]ection,
   restricted to AlgebraicGeometry. One hit, the elliptic normal-forms introductory comment.
4. `msearch.py ... leansearch` query: tensor product of translates of a section under
   a finite group action on a scheme. Eight hits on Action/Representation tensor,
   coinvariants and translations; no scheme-section norm definition. Full raw output
   retained in the sandbox scratchpad during preparation.
5. `msearch.py ... leanfinder` query: tensor product over finite group of pullbacks of
   an invertible sheaf and norm of a global section. Eight hits including Hilbert 90,
   pullback of free sheaves and ring Picard groups; no such scheme norm construction.
6. `msearch.py ... grep` query:
   actionNormBundle|actionNormSection|normSection|norm_section|tensorNorm. Zero hits.
7. Project/source rg for normSection, norm_section, normPencil, and separatingPair;
   the finite-morphism norm theorem was found but has a different input and conclusion.
   `grep -rn lem-sfb-separating-pair-open lean/WeilConjectures` found no declaration.
8. DAG concept search and `tools/blueprint_refs.py search 'tensor norm'` (zero blueprint
   matches), followed by reading related nodes, found the now-landed
   `lem-sfb-ample-curve-two-section-pencil`. Its exact norm definitions are reused,
   now with a definition node owning them rather than a theorem statement dependency.
   Searches for tensorPowIso, tensorPowerIso, tensorPowFunctor and pullbackTensorPowIso
   also led to the existing boundary comparison definitions, which are reused.

No STATEMENT-DISPUTED issue or source correction is needed. This is a statement delivery;
the only postponed theorem is the main theorem, carrying the matching DAG node and the
complete proof plan in its docstring.

## New nodes

`def-sfb-pencil-orbit-bundle-norm` registers the already published construction in
`Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`, using `existing: true` and no new
Lean module. Its main declaration is `AlgebraicGeometry.Scheme.Modules.pencilOrbitBundle`;
`lean.declarations` lists all seven definitions: `pencilGroupElements`,
`pencilTranslateTensor`, `pencilOrbitBundle`, `pencilUnitPowerIso`,
`pencilTranslatePowerIso`, `pencilTranslateSection`, and `pencilNormSection`.
These are the norm construction of de Jong §3.4(b)-(c), p.606, made explicit using
Stacks 01CA/01CD and the canonical pullback comparisons. The source is the same
norm-section replacement already approved for the item, with no new existence claim.
The node states the actual finite-family generality of the definitions: arbitrary
finite G, a family of automorphisms, any module L, and every natural exponent d.
Thus it does not add group-law, ampleness or invertibility hypotheses that their
signatures do not require. The empty list is the tensor unit, and its norm section
is 1; the empty-family power comparison is the inverse repeated unitor. At a list
cons, the exact `boundaryPullbackPowIso` and `tensorPowTensorObjIso` implement the
specified comparison. Pullback of sections is the normalized `1 tensor s` unit from
`tensorPullbackSectionAdjunction`. The resulting tensor section is transported into
the literal power of `pencilOrbitBundle`, exactly as the node says. These bodies have
real data and do not call `exists_ample_curve_two_section_pencil`.

The new node cites the existing owners of scheme, module, pullback and tensor notions,
and `def-sc-tensor-pullback-power-comparison` for its actual canonical comparison.
There was no definition node owning the orbit bundle or section norm. The existing
theorem node lists these helpers but is not a definition owner, which is precisely
the return's reason. The required new-node search was repeated on this repair:

- LeanSearch: `Tensor product of pullbacks of a sheaf over a finite group and the norm
  of a global section`. Eight hits on seminorms, Cartesian sheaves, ordinary module
  tensors and free sheaf pullback; no scheme orbit-bundle or norm construction.
- LeanFinder: `Orbit bundle tensor product of translated line bundles and norm section
  under a finite group action`. Eight hits on representation coinvariants and their
  tensor products; no scheme-module section norm.
- Mathlib grep through msearch: `pencilOrbitBundle|pencilNormSection|normSection|tensorNorm`,
  restricted to AlgebraicGeometry: zero hits.
- Project and DAG rg with these names and orbit/tensor-translates phrases finds the
  existing `AmpleCurveTwoSectionPencil` definitions and their theorem record, but no
  definition owner. `blueprint_refs.py search 'orbit bundle'`: zero blueprint matches.
  The three tool outputs are retained as returned in `mathlib_searches`, together with
  the project/DAG search result. No duplicate definition was written.

`blueprint_refs.py ancestor lem-sfb-separating-pair-open` returns None for this created
branch. The new node therefore preserves the item's null ancestor, prepends the item to
its exact `via`, and gives the precise original-curve norm construction in `from.place`.

## Second reading by NF

This dispatcher worker reread the returned item, saved packet, current main node,
all seven existing definitions and their docstrings, and the new ownership node.
No second agent was started, as the dispatch brief forbids it; the maintainer provides
the independent review. The repair addresses the single numbered H2 point in the
return: the theorem dependency is removed and replaced with
`def-sfb-pencil-orbit-bundle-norm`, which owns the existing definitions. The definition
record has no `file`, has `existing: true`, and its `statement` is the exact
`def pencilOrbitBundle` signature read from the published file. Its helper list includes
the unit-power comparison as well as every definition explicitly named by the return.

I checked the item signature again: the smooth projective geometrically integral
finite-type dimension-one F-curve, faithful finite action, and ample invertible L
have the same binders; the bound is still one n0 for every n above it; an arbitrary
finite basis supplies the two coordinate vectors; W is nonempty as a scheme over F;
every extension-field point through W gives generating norm sections in the actual
pullback B_E^n; the induced coordinate map is finite, surjective, invariant under
every base-changed group element, and etale on a nonempty source open. The coordinate
sum and base-change comparison use the existing norm with exactly the same directions.
The ownership correction changes none of these clauses or the canonical constructions.
I rechecked the trivial group, wild characteristic, finite field with no rational
parameter point, and empty coordinate basis cases. For the new general definition,
I also checked the empty finite family, empty translated list, zero module, d = 0,
and arbitrary families that are not group homomorphisms: its recursive definitions
remain well typed and require no added hypotheses. There is no statement correction,
new sorry, or disputed mathematical clause.
