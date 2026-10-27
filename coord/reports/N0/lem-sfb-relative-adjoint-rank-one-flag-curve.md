## Worker report

States `AlgebraicGeometry.exists_relativeAdjointRankOneFlagCurve` in
`Sheaf.AlgebraicGeometry.GroupScheme.RelativeAdjointRankOneFlagCurve`. The only theorem
proof is `sorry`; all definitions are actual predicates or structures with explicit data.
No existing node statement is corrected. The item changes only `lean` and gains four
statement dependencies: the new pointed-curve definition and three landed terminology nodes.

Read the item and every original statement dependency, including their full recorded
interfaces. The former CompactObject example module is withdrawn; its node now records
WeilConjectures.CategoryTheory.CompactObject. Followed the current module-mode header.
Read Conrad's PDF online, Proposition 4.2.7 and its proof, printed pp.123--124, especially
the construction before trivializing the pointed curve, and the referenced quotient
Theorem 2.3.6, pp.72--75. Source:
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . Also read the latest blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3): this supplies the inherited
unit context, rather than a direct statement of this structural lemma.

Hypothesis-by-hypothesis correspondence:

- Nonzero commutative Noetherian A is `(A : Type u) [CommRing A] [Nontrivial A]
  [IsNoetherianRing A]`. The base throughout is `Spec (.of A)`.
- The relative group schemes are `G T : Grp (Over (Spec (.of A)))`. This uses Mathlib's
  `GrpObj` group diagrams, also over a ring base, with no copied group structure.
- Smooth affine finite type G is `[Smooth G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`. Since the base is affine,
  affineness of its total space agrees with affineness over the base.
- Geometric connectedness and absence of nontrivial smooth connected normal unipotent
  subgroups are `hred`, using `ReductiveTorusCentralizer.IsReductive` on every pulled
  geometric group. That predicate uses the recorded faithful matrix unipotence predicate.
  Its additional algebraic-closure test is equivalent over algebraically closed Ω.
- Geometric semisimple rank one is `hrank`, using `RankOneRoots.HasSemisimpleRankOne`:
  the radical has the largest smooth connected normal solvable subgroup property, the
  quotient is an fppf quotient, and every maximal torus has dimension one.
- T is a closed group inclusion via `iT` and `IsClosedImmersion iT.hom.hom.left`.
  `hsplit` is existence of a group isomorphism with the actual Laurent split torus of
  some rank r, including r=0; `hmax` says its geometric inclusions are maximal tori.
- Trivial scheme-theoretic centre is `hcenter`: a point commuting with every point
  after every map W→V is the identity. It tests all schemes, hence all algebra extensions,
  including nonreduced ones. Affine tests and arbitrary tests agree by affine-local
  gluing for the represented group functor. No rational-point substitute is used.
- Zariski locality is `∀ s, ∃ U, s ∈ U ∧ ...`, with the group, torus and inclusion
  canonically pulled back by `Over.pullback U.ι`.

Conclusion clause correspondence, opening `RelativePointedFlagCurve`:

- `B`, `i`, `closed`, `contains`, `smoothB` give a smooth closed subgroup containing T;
  `connectedB` tests connectedness on every geometric fibre (empty is not connected).
- `X`, `smoothX`, `properX` give the smooth proper representing S-scheme; `p` is its
  quotient map. `quotient` tests the pulled quotient for every S'→S. In
  `IsRelativeRightCosetQuotient`, the equality criterion is g⁻¹h in the image of B(V),
  and all sections have lifts on a jointly surjective flat lfp covering. Since
  representables are fppf sheaves, this is precisely the sheafification of right cosets.
  It does not claim every section is globally represented by a coset representative.
- `action : ModObj G.X X` contains the scheme action and both action laws.
  `equivariant` says p(gh)=g·p(h), fixing it to the descended left multiplication.
- `σ` and `identitySection` specify σ=p∘e. `fixed` tests B-fixity on all V-points.
- `geometric` uses an isomorphism in `Over (Spec Ω)` to
  `ProjectiveSpace (ULift (Fin 2)) (Spec Ω)`, exactly two homogeneous coordinates.
- The second clause of `geometric` tests every Ω-scheme V. The domain of the multiplicative
  equivalence in `IsFlagCurveAutomorphismAction` is G(V), obtained by composing V→Spec Ω
  with the geometric point. Its codomain is `Aut` of X pulled to V, in `Over V`.
  The equation on every W→V identifies the equivalence with the given left action;
  testing W equal to the pulled X pins the whole morphism. It also forces naturality,
  so these equivalences give the induced group-sheaf isomorphism. Mathlib's Aut product
  is composition in the correct order for a left action (`Aut_mul_def`).
- `baseChange` gives an action on each canonical pullback and its first-projection
  compatibility (`IsFlagCurveActionPullback`). The pulled identity section is specified
  by the pulled group unit and p, with its first projection equal to σ. Thus action,
  quotient and section commute with arbitrary base change, including identity maps.

Dependency declarations used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Mathlib.CategoryTheory.Monoidal.Grp and Cartesian.Over: `GrpObj`, `Grp`, `Over.pullback`
  and its group functor. The recorded field group-scheme notion applies unchanged over S.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth, FiniteType, QuasiCompact,
  ClosedImmersion, Proper: `Smooth`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsClosedImmersion`, `IsProper`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, with an explicit `Spec Ω → S`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: canonical pullbacks,
  as used by `Over.pullback` and `ProjectiveSpace`.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: `ProjectiveSpace` and its structure map.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing:
  `RingGroupSchemes.splitTorus` (rank-zero terminal product included).
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces:
  `RankOneRoots.HasSemisimpleRankOne`.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Mod: `ModObj` and the induced Hom action.

The already stated proof dependencies BorelMaximalTorusConjugacy, BorelSchemeNormalizer,
and ProjectiveSpaceStandardCharts are plain imports; their signatures and docstrings were
read. Other proof dependencies have no recorded Lean module in the current DAG; their
seven-step proof plan is preserved in full in the theorem docstring, without placeholders
or newly postulated theorems for those inputs.

Edge cases checked: rank zero is permitted as an input splitting, although incompatible
with geometric adjoint semisimple rank one; no artificial positivity hypothesis is added.
Characteristic two is retained; there is no invertibility-of-two or characteristic bound.
Nonreduced A, W, S' and algebras are admitted; hcenter and Aut tests retain them.
Disconnected A is admitted. The zero ring is excluded exactly as in the node.
Empty base-change schemes and empty test schemes remain admitted, including the empty
fppf covering where appropriate. No affine or finite-type restriction is imposed on
base changes or test schemes. All objects/tests share universe u; `ULift (Fin 2)` supplies
the required projective-coordinate universe and excludes no coordinate case.

Searches actually made via msearch.py: LeanFinder, “An adjoint rank one reductive group
scheme with split maximal torus has a smooth proper pointed quotient with projective line
geometric fibers”: OnePoint/Weierstrass/AffineSpace/Proj hits, no theorem match. Loogle,
“GrpObj, IsReductive”: zero hits, unknown identifier GrpObj. Mathlib grep,
“Reductive|Borel|flagVariety” under AlgebraicGeometry: zero hits. For the new notion,
LeanSearch “Pointed flag curve quotient of a relative group scheme with arbitrary base
change and geometric projective line automorphism sheaf”: eight Weierstrass base-change
hits; LeanFinder “Pointed flag curve quotient group scheme projective line automorphism
sheaf”: eight unrelated projective-point/AffineSpace hits; Mathlib grep
“flagCurve|PointedFlag|pointed.*flag|flag.*curve”: zero hits. Actual responses are in the
new node's mathlib_searches. Project/source rg by node id had no match. Broader project
search found and reused the field predicates and ring split torus above. No matching
relative pointed flag-curve definition or theorem exists. `blueprint_refs.py search
'flag curve'`: zero matches. No STATEMENT-DISPUTED flag or source correction is needed.

## New nodes

`def-sfb-relative-pointed-flag-curve` owns RelativePointedFlagCurve and its three predicate
helpers, each with source/blueprint docstrings. This is data for a specified relative
homogeneous pointed curve, not an existence assertion; no reductivity, torus splitting
or rank hypothesis is built into the definition. The source is Conrad Proposition 4.2.7,
proof, pp.123--124, and Theorem 2.3.6. It supplies the previously absent relative nonnormal
quotient with the action, section, arbitrary-base-change comparison and geometric full
Aut-sheaf property. Searches above found only field homogeneous-quotient theorems and
IsFppfGroupQuotient (which requires a normal kernel and a group quotient), so none gives
this notion. Its data has no sorry and uses canonical pullbacks; no arbitrary substitute
for the induced action or map is assumed.

## Validation

Both delivered modules were compiled individually in dependency order using scompile.py;
no warnings or errors (the theorem's expected sorry warning alone is permitted).

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
