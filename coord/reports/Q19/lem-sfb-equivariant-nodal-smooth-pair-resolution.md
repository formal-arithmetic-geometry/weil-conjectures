## Worker report

`Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution` states
`AlgebraicGeometry.exists_equivariant_nodal_smooth_pair_resolution`, with its proof `sorry`.
Its docstring contains all fifteen proof steps and their node uses verbatim (line wrapping only).
The stage-1 live split is current and reviewed by NC but has no Lean record; it is not a completed
stage-2 statement. The sandbox initially contained only search logs, not a prior delivery.

The Lean signature renders every hypothesis as follows:

| Node clause | Lean |
| --- | --- |
| Arbitrary field F | `(F : Type u) [Field F]`; no algebraic-closure or perfection hypothesis |
| Integral finite-type F-scheme S | `s : S ⟶ Spec (.of F)`, `IsIntegral S`, `LocallyOfFiniteType s`, `QuasiCompact s` |
| Closed D | `D : Closeds S` |
| Projective-bundle, flat, finitely presented f | `hf : IsProjectiveBundle f`, `Flat f`, `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f` |
| Nonempty connected reduced one-dimensional nodal geometric fibres | `hfib : HasNodalGeometricFibres f` and `GeometricallyReduced f`; the former contains connectedness including nonemptiness, dimension 1, and the exact two-variable completed-local-ring quotient |
| Smooth geometrically integral generic fibre | `η`, `hη : IsGenericPoint η Set.univ`, `Smooth (f.fiberToSpecResidueField η)`, `GeometricallyIntegral` of the same map |
| Smooth over S minus D | `hsmooth`, membership in the relative `f.smoothLocus` |
| Finite disjoint smooth sections | `n : ℕ`, `m : Fin n → (S ⟶ T)`, `hm`, `hdisjoint`, `hmark` |
| Closed marked boundary | `B : Closeds T`, `hB` identifies it with precisely the union of section images and `f ⁻¹' D`; B is determined, not a larger exceptional set |
| Finite group acting on F,T,S compatibly | `J : Type v`, `Group J`, `Finite J`, ring-automorphism homomorphism `ρ`, scheme-automorphism homomorphisms `aT`, `aS`, `heq`, and `hscalar` |
| Semilinear scalar convention | `Spec.map (ρ g⁻¹).toRingHom`; the inverse compensates for contravariance of Spec, and permits every action on F |
| D and M stable | `hD`, `hM` are equality of images, including permutation of sections |
| Split marked nodal graph | `hsplit : IsSplitMarkedNodalAction f aT aS n m`, defined in the new node below |
| Equivariant projective birational surjection t | `ht : IsProjectiveBundle t`, `Surjective t`, `htbir` (commuting dense-open isomorphism), `a₀`, `heqt` |
| Integral smooth S₀ | `IsIntegral S₀`, `Smooth (t ≫ s)` |
| Reduced inverse image of D is relative SNC | `hE`, on the radical of the canonical comap of `vanishingIdeal D` |

The Lean conclusion renders every clause as follows:

| Node clause | Lean |
| --- | --- |
| Resolution of the specified fibre product | `r : T' ⟶ pullback f t` |
| Integral smooth T' over F | `IsIntegral T'`, `Smooth (r ≫ pullback.snd f t ≫ t ≫ s)` |
| Projective birational surjective r | `IsProjectiveBundle r`, `Surjective r`, and its commuting dense-open isomorphism |
| Same properties for T' → T | the same three clauses for `r ≫ pullback.fst f t` |
| J-equivariance | `a' : J →* Aut T'`; the two displayed equations for the projections characterize equivariance into the diagonal fibre-product action jointly, without an arbitrary action on the pullback |
| Isomorphism off the prescribed boundary | for every open with carrier the complement of `(pullback.fst f t) ⁻¹' B`, `IsIso (r ∣_ U)` |
| Exact reduced inverse image E' | equality to `((vanishingIdeal B).comap (r ≫ pullback.fst f t)).radical` |
| Relative SNC boundary | `E'.IsSmoothStrictNormalCrossingsDivisor` for the F-structure map |
| All local rings regular | `IsRegularScheme T'`, reusing the recorded locally-Noetherian plus stalkwise-regular definition |
| Distinct component equations in ordinary local rings | a finite family of integral noncontained closed components `C` with intersection of ideals equal to E', and for each x a regular parameter list plus an injective assignment from components through x to its positions. Extension of each component ideal along the affine germ is the principal ideal of its assigned parameter. This states the equations at x, not in an etale extension. |
| Finite-projective-space convention preserved | `IsHProjective (t ≫ s) → IsHProjective (r ≫ pullback.snd f t ≫ t ≫ s)` |
| Equality of function fields | dense-open isomorphisms commute with the given morphisms, so the induced map of generic stalks/function fields is an isomorphism. On the integral schemes here this is exactly birationality, not an unrelated abstract field isomorphism. Integrality of the fibre product follows from flatness and the geometrically integral generic fibre, as the node's step 3 explains. |

Dependency declarations were read, including their full definitions and docstrings:
`Field` (Mathlib.Algebra.Field.Defs); `Smooth` (Mathlib.AlgebraicGeometry.Morphisms.Smooth);
`IsIntegral` (Mathlib.AlgebraicGeometry.Properties); `LocallyOfFiniteType` and `QuasiCompact`
(the recorded morphism modules); `IsProjectiveBundle`
(Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism);
`Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`
(Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor);
`Flat`, `LocallyOfFinitePresentation`, `IsClosedImmersion` (their Mathlib morphism modules);
`pullback` and its projections (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback);
`GeometricallyIntegral` and `GeometricallyIrreducible` (the Mathlib geometric-property modules);
`IsRegularScheme` (Sheaf.AlgebraicGeometry.IsRegularScheme);
`IsLocalRing.IsRegularSystemOfParameters` (WeilConjectures.RingTheory.IsRegularSystemOfParameters);
`IsHProjective` (WeilConjectures.AlgebraicGeometry.Morphisms.Projective);
`HasNodalGeometricFibres` (Sheaf.AlgebraicGeometry.NodalGeometricFibres).
Closed subschemes and their ideals use `Scheme.IdealSheafData`, not a duplicate notion.
The withdrawn CompactObject example was followed through its current node record to
WeilConjectures.CategoryTheory.CompactObject and read there.

Source checked: `pdftotext -f 155 -l 156` on the local ILO PDF, printed pp.149--150.
The one-curve step and the relative-field refinement are both explicit on p.149.
No change to the item's mathematical statement, proof, or proof dependencies is proposed.

Edge cases checked: n=0 and empty D give unit ideals/empty divisors and the complement is all
of the fibre product; empty component families and dimension-zero parameter lists remain
allowed. The identity base modification is allowed with no extra condition. Nonempty integral
S and nonempty fibres exclude empty T without an added hypothesis. The finite group can be
trivial, act nonfaithfully, and act nontrivially on F. Group universe v is independent of u.
Self-nodes are allowed by the split predicate; its normalization-point clause distinguishes
both ends even when they lie on the same component. No separatedness of S over F, no normality
of S, no characteristic restriction, and no smoothness of fibre components is introduced.
The closed marked boundary B is determined by hB; it exists since f is projective and its
sections are closed. Finite presentation is given as LFP plus QC plus QS, as in its recorded node.

Searches (all via the prescribed msearch wrapper): LeanFinder, “equivariant resolution of a
split marked nodal curve over a smooth normal crossings pair”, returned smooth morphism and
normalization declarations, no exact theorem. Loogle on HasNodalGeometricFibres and
IsProjectiveBundle returned unknown identifier/no hits. Mathlib grep `Nodal|[Bb]irational|[Ss]plit`
in AlgebraicGeometry returned only general birational files and unrelated elliptic-curve
splitting. LeanSearch, “split marked nodal curve group action fixes dual graph branches and
marked sections”, returned unrelated group actions; no exact predicate. Searches of
lean/WeilConjectures and lean/Sheaf found the algebraically-closed nonequivariant
`exists_nodal_pair_projective_resolution`, which is not the item. They also found
MarkedSplitNodalTower and HasStrictSplitNodalFibres, which impose smooth fibre components
and exclude self-nodes. HasQuasiSplitNodalFibres supplies just rational nodes and branches.
DAG searches for split nodal and dual graph found no predicate of exactly this statement;
`tools/blueprint_refs.py search 'split nodal'` returned zero blueprint nodes.
The new node records the original wrapper result records and project/DAG searches.

Compilation uses scompile.py only. The new definition compiled cleanly in both sandbox and
library modes. The initial main-file import check found four legacy non-module proof-only
modules, which even `import all` cannot import from required module mode:
Sheaf.AlgebraicGeometry.FunctorialFanDesingularization,
Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent,
Sheaf.AlgebraicGeometry.LogFanChartBlowup,
Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison.
The first source was confirmed on the current server using scompile.py --source.
These four proof-only imports are omitted and reported for maintainer module migration;
all their proof steps and DAG proof dependencies are retained. All other recorded proof
modules are imported privately. No source or live library file was modified.

## New nodes

`def-sfb-split-marked-nodal-action` defines `IsSplitMarkedNodalAction`. It reuses the landed
HasQuasiSplitNodalFibres and componentwise reduced normalization, requires geometrically
irreducible reduced fibre components, and fixes components, nodes, normalization ends and
marked legs under base-point stabilizers. The canonical induced automorphisms are specified
by their commuting squares and quantified universally; they are uniquely determined by
these squares, so neither an arbitrary map nor a choice of action is supplied as an input.
This is exactly the input convention of the item's split marked graph clause. It does not
require smooth components, which is why HasStrictSplitNodalFibres cannot be reused instead.
Source: ILO X p.149, the one-curve resolution input, together with the convention explicitly
stated in this item's live DAG statement. The searches above found no existing exact predicate.
The definition has real logical data, no sorry, and no new theorem.

## Second reading by Q19

Author's final clause audit, not an independent review: I compared the live node, both Lean
files and the new definition node. No source-based statement correction was needed. The
section-union boundary is exact, the isomorphism and reduction concern the pullback boundary,
while the composite back to T retains its own birational and projectivity assertions. Both
projectivity conventions remain separate. Branch fixing is present even for a self-node;
the input does not silently substitute the stronger strict-split tower definition. Independent
review is the maintainer's responsibility under this dispatcher brief; no other agent was started.

Final scompile.py validation: both delivered files clean in sandbox and library mode;
SplitMarkedNodalAction took 2.2--2.3 s and EquivariantNodalSmoothPairResolution 3.2--3.6 s.
The notation checks fixed the category argument on pullbacks occurring in Set coercions
and replaced a line-broken field projection by the fully qualified predicate. No mathematical
hypothesis or conclusion changed during elaboration repair.
