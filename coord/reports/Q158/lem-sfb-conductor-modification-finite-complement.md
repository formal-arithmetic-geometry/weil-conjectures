## Worker report

The module `Sheaf.AlgebraicGeometry.ConductorModificationFiniteComplement` states
`AlgebraicGeometry.conductor_modification_finite_complement`, with its sole theorem proof
`sorry`. The helper `AlgebraicGeometry.conductorModificationMap` is defined in full by
`IsPushout.desc`, using the supplied branch compatibility. It is the canonical induced
morphism, not an arbitrary morphism or a choice from an undetermined existence theorem.
Its equality proof merely composes the stated equality with the pushout cocone leg.

The source was read in `literature/stacks-project/varieties.tex`, the lemma labelled
`lemma-modification-normal-iso-over-codimension-1` (Tag 0BFP), clauses (1),(2), and
`literature/stacks-project/more-morphisms.tex`, the proposition labelled
`proposition-pushout-along-closed-immersion-and-integral` (Tag 0E25), including its explicit
compatibility with restriction to compatible open subschemes. The eight-step DAG proof
is included in the theorem docstring, with the dependencies of each step. The newest
blueprint path `literature/blueprint/latest/` was searched; the source place for this
agent-created refinement is the two Stacks passages, not an older blueprint snapshot.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| DVR R; fraction field K, residue field k, S = Spec R | Explicit `R : Type u`, `CommRing R`, `IsDomain R`, `IsDiscreteValuationRing R`; base `Spec (.of R)`. K is the canonical `FractionRing R`; the special fibre is expressed by the canonical `IsLocalRing.closedPoint R`, whose residue field is the canonical residue field. No extra choice of either field is needed. |
| C,W projective, flat, finitely presented over S | `C W : Over (Spec (.of R))`, with the respective `IsHProjective`, `Flat`, `LocallyOfFinitePresentation` instances. Projectivity gives quasi-compactness and separatedness, so local finite presentation is finite presentation here. |
| B,N finite etale over S; B to N finite etale constant degree two | `B N : Over ...`, `IsFinite B.hom`, `Etale B.hom`, and the corresponding N instances; `j : B ⟶ N`, `Etale j.left`, `j.left.IsFiniteLocallyFreeOfDegree 2`. The last class includes finiteness and specifies rank two on every fibre. |
| Supplied closed immersions B into C,W in relative smooth loci | `iC : B ⟶ C`, `iW : B ⟶ W`, `IsClosedImmersion` instances on their underlying scheme maps, `hiC` and `hiW`. |
| Empty B,N allowed | No nonemptiness binder on either scheme, j, or the images. The rank condition over an empty N is vacuous. |
| Both scheme pushouts and their structure morphisms | `X Y : Over ...`, legs `a,b,aW,bY` in Over; `hX` and `hY` are `IsPushout` in **Scheme**, not just in Over. Thus their universal properties test all scheme targets. |
| Cartesian squares | `hcartX`, `hcartY : IsPullback ...`. |
| Finite surjective curve-to-pushout maps and closed N-maps | `IsFinite a.left`, `Surjective a.left`, `IsClosedImmersion b.left`, and their Y analogues. |
| All inverse-image open squares are pushouts | `hOpenX`, `hOpenY`, quantified over every open. Their two upper arrows are obtained by the canonical `Over.pullback V.ι` functor on the actual diagram, with hX.w or hY.w giving the commutation equality. The lower arrows are `pullback.snd`. |
| X,Y projective flat finitely presented, with the same nodal fibre condition | The respective projectivity, flatness and local finite presentation instances; the last again implies finite presentation here. |
| Nodal geometric fibres for C,W,X,Y, possibly disconnected | `hnodal` quantifies over the four-element list of the four actual Over objects, then every algebraically closed `Ω : Type u` and geometric point `g`. It requires `Nonempty`, `IsReduced`, `IsPureDimension 1` and, for each nonsmooth closed point, `IsGeometricOrdinaryDoublePoint Ω ... x`. No connectedness is imposed. Smoothness at the point is the existence of a smooth open neighbourhood; the completed local ring is exactly that of the actual geometric fibre stalk in the existing ordinary-double-point definition. |
| C minus B is X minus N, W minus B is Y minus N | `hcomplX`, `hcomplY` specify opens whose underlying sets are precisely the complements of the branch and N images, with scheme isomorphisms whose composites with the open inclusions are the given curve-to-pushout map. |
| r a specified finite composition of blowups at reduced closed special-fibre points | `r : T ⟶ C`, `A : OrdinaryBlowupTower C.left`, `eT` identifying T with the last level, `heT` identifying its actual composite with r. `hcentres` requires each ideal be the canonical `vanishingIdeal` of a closed singleton, and requires its image in Spec R be the closed point. Thus no arbitrary thickening or omitted intermediate centre is allowed. |
| T regular and a finite disjoint union of integral surfaces of dimension two | `hregular : IsRegularScheme T.left`; `hcomponents` supplies finitely many pairwise disjoint opens covering T, each integral and of topological Krull dimension two. A finite open partition is exactly a finite disjoint-union decomposition into its open subschemes; there is no integral or connected hypothesis on the whole T. |
| q proper, W reduced | `q : W ⟶ T`, `IsProper q.left`, `IsReduced W.left`. |
| Birationality on matched components, in the node's specified sense | `hgeneric` is `Set.BijOn q.left` between the sets of component-generic points, defined using `irreducibleComponents` and `IsGenericPoint`; `hstalk` requires `IsIso (q.left.stalkMap η)` at each such source generic point. This is exactly the interface of the recorded normal-modification lemma. |
| q_K an isomorphism | `hqK` is `IsIso` on the underlying scheme map of `(Over.pullback (Spec.map (algebraMap R (FractionRing R)))).map q`. Since q is an Over morphism, its base compatibility is present; the review's advisory about q being an S-morphism is therefore explicit. |
| h = rq restricts to iC on supplied B | `hB : iW.left ≫ q.left ≫ r.left = iC.left`. Lean composition reads left to right. |
| U_q maximal isomorphism open | `U : T.left.Opens` and `hU : IsGreatest {V | IsIso (q.left ∣_ V)} U`; this includes both that U is an isomorphism open and that every such open lies in it. |
| T minus U finite, all points closed and in the special fibre | The first two conjuncts: `((U : Set T.left)ᶜ).Finite` and the explicitly quantified closed-singleton/special-fibre assertion. |
| D exactly the image of that complement plus all centre images | The existential D satisfies `D = r.left '' Uᶜ ∪ ⋃ i, (A.toBase i.castSucc) '' (A.center i).support`. Since the centres are reduced closed singleton ideals, these are exactly the centres' point images, with no extra deleted points. |
| Z the image of D in X | `Z = a.left '' D`. |
| D,Z finite sets of closed special-fibre points | `D.Finite`, `Z.Finite`, and the two quantified assertions `IsClosed {z}` together with equality of the structure-map image to `IsLocalRing.closedPoint R`. |
| Canonical p is an isomorphism over X minus Z | An open V with `(V : Set X.left) = Zᶜ`, and `IsIso (conductorModificationMap ... (q.left ≫ r.left) hB hX hY ∣_ V)`. `morphismRestrict` has domain the actual inverse-image open, so the conclusion is the specified restricted morphism being invertible. |
| Includes N and persistent horizontal nodes | There is no subtraction of the N image in this final open. The only removed set is exactly Z. |

Dependencies used (the recorded signatures and docstrings were read):

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`;
  `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: colimit universal property;
  its pushout specialization `IsPushout`, `IsPushout.desc`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`;
  `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and open subschemes;
  the canonical restriction notation `∣_`;
  `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`, `Scheme.Hom.stalkMap`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`;
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace.Hom` underlying
  the actual scheme morphisms and local stalk maps.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`;
  `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- Already-landed definitions added to stmt_deps: `def-trf-ordinary-resolution-rule`
  (`Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`, `.toBase`);
  `def-trf-projective-nodal-tower`
  (`Sheaf.AlgebraicGeometry.ProjectiveNodalTower`: `IsGeometricOrdinaryDoublePoint` only,
  not its connected projective-nodal-curve predicate);
  `def-pc-finite-locally-free`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`). These are reused without new nodes or copies.

All modules of stated proof dependencies are imported with plain `import`. This includes
`Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne` and its exact
`normal_modification_isomorphism_open_contains` interface, the finite-closed-points theorem,
the properness modules, the regular-local-DVR result, and the blowup complement theorem.
Mathlib leaf dependencies have their declaring modules imported. No proof import was
omitted for a cycle.

Edge cases checked before writing: empty B,N; disconnected geometric fibres; empty
exceptional complement; a zero-length A (the union over `Fin 0` is empty, and eT makes r
an isomorphism); repeated centres and repeated images (unions remove multiplicities);
nontrivial residue extensions; points on N outside Z (they remain in V); components that
are distinct (the generic-point bijection matches them without assuming global
integrality). No completeness, excellence, perfection or characteristic restriction is
introduced. Finite type test fields and schemes live in the same scheme universe, not
an unrelated smaller universe. Every variable and universe is bound explicitly with both
auto-implicit options false. No statement correction or disputed statement is needed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A proper birational map to a regular surface is an
  isomorphism outside finitely many closed points and this descends through conductor
  pushouts”: 8 hits on normalization morphisms and properness; none states the result.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.Birational, AlgebraicGeometry.IsProper`:
  0 hits.
- `msearch.py ... grep`: `conductor|nodal|blowupSequence`, subdirectory AlgebraicGeometry:
  0 hits.
- `rg` in project `WeilConjectures` and `Sheaf` for the item id and
  `conductor_modification_finite`: no existing declaration.
- `rg` for nodal, conductor, blowup sequences/towers and isomorphism loci found the
  existing `ProjectiveNodalTower`, `OrdinaryResolutionRule`, `SurfacePointBlowupData`,
  `TraitEtaleBranchPinching`, and `NormalModificationCodimensionOne`. Their definitions
  and relevant theorem signatures/docstrings were read. The connected nodal predicates
  do not encode this node's possibly disconnected fibres, so only the common ordinary
  double point definition is used. The existing tower exactly supplies the needed
  centre data; no new blowup-sequence definition is introduced.
- The existing CompactObject example is withdrawn in the shared tree; its node points
  to `WeilConjectures.CategoryTheory.CompactObject`, whose header and docstrings were
  read as the current example.

Validation: `scompile.py Q158 lem-sfb-conductor-modification-finite-complement` compiled
both the sandbox and library module cleanly (3.2 s and 3.7 s). The earlier compiler pass
identified a parser error in a pipeline-style finite-set conjunct; it was replaced by
the explicit `((U : Set T.left)ᶜ).Finite`. There are no diagnostic commands, extra
postponed theorems, file-local declarations or proof-bearing data placeholders.

## Second reading by Q158

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
