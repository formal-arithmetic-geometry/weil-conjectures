## Worker report

This packet repairs all four points in the return on immutable head 2ab45bf89a8a.
The saved packet first passed `deliver2.py --no-push` (06e499e186); that check did not
detect the mathematical defect R1. The target's natural-language statement and proof
remain unchanged. Against the current shared node, only `lean` and additions to
`stmt_deps` change. The delivery wrapper rebases the packet on current newtargets-dag.

`Sheaf.AlgebraicGeometry.CompactlySupportedSections` defines the module
`AlgebraicGeometry.compactlySupportedSections A f F` and its inclusion. It is the span
of sections satisfying the landed `Etale.SectionHasProperSupport A F (Etale.mk (𝟙 X)) f`.
That predicate requires the closed set to equal the nonzero-geometric-germ locus and
uses the landed `Scheme.IsClosedSubsetProperOver` for its reduced induced properness.
There is no `SectionHasSupport` copy or inline reduced-support properness definition.
The new definition's domain now explicitly requires `LocallyOfFiniteType f`, as do
both landed predicates; in the target this follows from étaleness of the fibre projection.
The use of a span gives real submodule data without postponing closure proofs. Proper
support is stable under sums and scalars by closedness of section support, finite unions
of closed proper subsets and closed-subset inheritance, so this is the source's module.

The same module constructs the canonical maps: `canonicalFiniteCoproductMap` is the
finite sum of coproduct injections after the component maps (zero in the unused infinite
branch); `geometricFibreComponentMap` takes a terminal-object germ and applies
`Etale.upperStarCompSheafFiberIso`; `etaleGeometricFibreRestrictionMap` assembles them.
The new `etaleSectionPullbackToGlobal A r p a ha F` is a genuine linear map: the unit
of `Etale.upperStarLowerStarAdjunction` for `r`, evaluated at `Etale.mk p`, followed
by restriction from the base-changed object to the terminal object of `C`. In the
project's ordering the base change is `P ×_V C`, so that restriction is induced by
`(a, id_C)`; with the factors reversed it is the return's `(id_C, a)`.

`Sheaf.AlgebraicGeometry.EtaleGeometricFibreCompactSections` states
`AlgebraicGeometry.etaleGeometricFibreCompactSections`, with its sole proof `sorry`.
Each hypothesis and clause is rendered as follows:

| Node text | Lean rendering and check |
| --- | --- |
| Schemes `V,T`, separated quasi-compact étale `h:V→T` | `{V T : Scheme.{u}}`, `(h : V ⟶ T)`, `[IsSeparated h] [QuasiCompact h] [Etale h]`. |
| Algebraically closed field and geometric point | `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)`. |
| Fibre `C` and projection `r` | `pullback h t` and `pullback.fst h t`; the base map is `q = pullback.snd h t`. |
| Set `I` of lifts of `t` | `Scheme.Hom.GeometricFiber h t`, whose elements are exactly morphisms `v` with `v ≫ h = t`. |
| Finiteness of `I` | First conjunct `Finite I`, including empty `I`. |
| Canonical coproduct decomposition over Ω | Second conjunct `IsIso (Sigma.desc ...)`; its component is `pullback.lift v.1 (𝟙 (Spec Ω)) v.2`, so its composite with `q` is the identity. |
| Commutative ring `A`, sheaf of modules over the constant ring `A` | `(A : Type (u + 1)) [CommRing A]` and arbitrary `F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)`. “Constant-A” specifies the coefficient ring; it imposes no constant-sheaf hypothesis on `F`. |
| `G = r⁻¹F` | `(Etale.upperStar (ModuleCat.{u + 1} A) r).obj F`. |
| Proper support over `Spec Ω` | `Etale.SectionHasProperSupport A G (Etale.mk (𝟙 C)) q s`, not properness over `C`. It requires the actual nonzero-germ locus to be closed and reduced-proper. |
| `H⁰_c` and its stated natural A-linear isomorphism | Third conjunct makes the canonical composite `compactlySupportedSections.ι A q G ≫ etaleGeometricFibreRestrictionMap A h Ω t F` an `IsIso` in `ModuleCat A`. The factors are restriction, germs and the natural inverse-image stalk comparison; each commutes with sheaf maps. |
| Every global section has this support | Fourth conjunct quantifies all `s : (Etale.sectionsFunctor _ C).obj G` and asserts exactly `SectionHasProperSupport` above. |
| Pointed étale neighbourhood `W,w` | `(W : T.Etale) (w : Spec Ω ⟶ W.left)` and `hw : w ≫ W.hom = t`. |
| Étale lift over `T` and its section `z` | `(lift : W.left ⟶ V) [Etale lift]`, `hlift : lift ≫ h = W.hom`, and `z : F.obj.obj (op (Etale.mk lift))`. This is the morphism used as the étale-site object in the node. |
| Graph inside `P = V ×_T W` | `γ = pullback.lift lift (𝟙 W.left) ...`; the projection to `V` is `p = pullback.fst h W.hom`. |
| Extend by zero off that graph | Existential `zext : F(P→V)`; its germs at every geometric point outside `Set.range γ.base` are zero. |
| The extended section restricts to `z` | `F.obj.map (Over.homMk γ ...).op zext = z`, with the two étale objects explicitly specified. |
| Pull back this very `zext` to the fibre | The final equality applies `etaleSectionPullbackToGlobal A r p a ... F` to `zext`, where `a = pullback.lift r (q ≫ w) ... : C ⟶ P`. Its projections are `r` and `q ≫ w`; its commuting equation uses `hw` and `pullback.condition`. |
| Original germ in indexed summand and zero elsewhere | `etaleGeometricFibreRestrictionMap ... (pullback(zext)) = Sigma.ι ... ⟨w ≫ lift, ...⟩ (germ_w(z))`. A single coproduct injection simultaneously states its indicated component and all the zero components. There is no existential unrelated `sC`. |

The dependency declarations used are:

- Mathlib `AlgebraicGeometry.Scheme`, `IsSeparated`, `QuasiCompact`, `Etale`,
  `LocallyOfFiniteType`, `IsProper`, `IsAlgClosed`, and
  `CategoryTheory.Limits.pullback`, its projections and lifts, in their recorded modules.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`:
  `AlgebraicGeometry.Scheme.Hom.GeometricFiber`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the project's constant-coefficient
  module-sheaf convention `Sheaf _ (ModuleCat A)`; no private module-sheaf category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`:
  `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`.
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`:
  `AlgebraicGeometry.Etale.sectionsFunctor`.
- Mathlib `Scheme.pointSmallEtale`, `GrothendieckTopology.Point.sheafFiber` and
  `toPresheafFiber`, for actual geometric stalks and germs.
- `Sheaf.AlgebraicGeometry.EtaleSectionProperSupport`:
  `AlgebraicGeometry.Etale.SectionHasProperSupport` (def-cbc-etale-section-proper-support).
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.IsClosedSubsetProperOver`
  (def-weil-pbc-closed-subset-proper-over-base), whose definition uses the canonical
  `vanishingIdeal` reduced induced subscheme. The recorded reduced-induced theorem is
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme` in
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.

Edge cases checked: empty fibre gives empty `I` and zero section modules and coproduct;
zero section has empty proper support; arbitrary module sheaves are allowed; a zero germ
of `z` gives zero in every summand; with two point components and nonzero `z`, `a` selects
precisely the graph component so the other coordinate vanishes. This last check detects
R1: bijectivity of Φ alone cannot give the claimed equality for `pullback(zext)`.
For identity base change the helper is the ordinary adjunction-unit pullback followed by
terminal restriction; it never chooses an inverse image under Φ. All universes and
variables are explicit. No statement dispute or target statement correction remains.

Searches retained from the saved packet: `msearch.py leanfinder` query
“compactly supported sections etale geometric fibre direct sum geometric stalks” found
only structure-sheaf/stalk lemmas; `loogle` query “GeometricFiber, properSupport, H0,
sheafFiber” reported unknown `GeometricFiber` and no hits; `grep` query
“properSupport|H0_c|H0c|compactSupport” in Mathlib gave no hits.
The repair repeated the three kinds: LeanSearch on “The module of compactly supported
global sections of an etale module sheaf with proper geometric support” returned generic
ideal support, ordinary sections and function `HasCompactSupport` (digest a0bfdaa6e25482d6);
LeanFinder on “The submodule of global sections of an etale module sheaf whose support is
proper over a base scheme” returned `ModuleCat.Tilde.sectionsSubmodule` and algebraic
étale-locus lemmas (digest 13ec4d33b9c2f0aa); grep on
`compactlySupportedSections|SectionHasProperSupport|IsClosedSubsetProperOver` under
Mathlib/AlgebraicGeometry gave zero hits (digest 4f53cda18c2baa0c).
`rg` on the upstream and project Lean trees found the two landed support predicates;
they are now reused. The project `geometricFibreSectionRestriction` is specialized to a
pointed base-change square and its ordered iterated pullbacks; the helper here exposes
unit-and-restriction for any étale `p` and specified map `a` over `V`.
Direct DAG searches find the existing support nodes and no separate compact-section
module node. The retained new node therefore supplies the module, not another support
notion. All new map data is constructed, not chosen from a postponed theorem.

## Second reading by Q51

I made a separate second pass with the node, both modules, the landed support definitions,
and Stacks 09Z9, 0F4Y, 0F4L and 04FT open. The dispatcher forbids starting another agent;
this section records my own second reading, not an independent reader's approval.

1. The node's separated, quasi-compact, étale `h` appears with exactly those three instances;
   neither finiteness nor properness is assumed. The algebraically closed field and geometric
   point have the same scheme universe. The commutative ring and arbitrary constant-ring
   module sheaf match the source; `F.IsConstant` remains absent.
2. `C`, `r` and `I` are respectively the chosen fibre product, first projection and the
   actual Ω-lifts. The first conjunct is finiteness; the second uses the canonical lift
   of each `v`, with second projection identity, giving the promised isomorphism over Ω.
3. The inverse-image sheaf in the support module and in the component germ map is the
   same `r⁻¹F`. The third conjunct is `IsIso` of the explicit canonical composite from
   `H⁰_c`; it is not a choice of some isomorphism. Its component is terminal germ followed
   by the inverse-image germ identification, as the node asks, and all factors are linear.
4. The fourth conjunct now states proper support for each actual section using the landed
   predicate. Reading that definition shows equality with the nonzero-germ locus and
   properness of the reduced induced subscheme over `q : C → Spec Ω`. The new module's
   span uses exactly that predicate. R2's duplicate `SectionHasSupport` is deleted, and
   no inline `IsProper (vanishingIdeal ... ≫ f)` remains. Both landed nodes are cited.
5. For the final clause, `W`, `w`, `lift`, `hw`, `hlift` and `z` match the pointed étale
   neighbourhood and lifted section. The graph has projections `lift` and identity.
   The first condition on `zext` is zero germs outside the graph, for every geometric
   point; the second is restriction along that graph equal to the given `z`.
6. I followed the final equality's argument rather than just its right side: the displayed
   `a : C → P` has components `r` and `q ≫ w`, so `a ≫ p = r`. The helper applies the
   inverse-image unit for `r` at the object `p`, then restricts along `(a, id_C)` in
   `P ×_V C`. Its input is the very `zext` from the previous two conditions. The equality
   is therefore Φ of its pullback, as R1 requires. The old unrelated `∃ sC` is gone.
7. The right side is the injection indexed by `w ≫ lift` of the germ of `z` from the
   pointed object `(lift,w)`. It states the nonzero coordinate and every zero coordinate
   in one coproduct equality. Empty fibre, zero coefficients, identity maps and two
   distinct components do not erase the link to `zext`.
8. The new definition node introduces all its objects, states the locally finite-type
   domain of the reused support interface, and cites that interface and reduced properness.
   Its declaration is a `def` under the module-wide `noncomputable section`, so the recorded signature matches the extractor while retaining the required noncomputable semantics. All helper names
   are listed in `lean.declarations`, and the new helper has real data and a source docstring.

The four return points are thus repaired: R1 by the actual section pullback, R2 by landed
support predicates, R3 by this clause-by-clause second pass, and R4 by the verbatim signature.

## New nodes

`def-sfb-compactly-supported-sections` is retained from the returned packet. It defines
the A-module generated by properly supported global sections for a locally finite-type
scheme morphism. Its support and reduced properness notions are the landed nodes
`def-cbc-etale-section-proper-support` and
`def-weil-pbc-closed-subset-proper-over-base`; it adds neither predicate again.
The source is Stacks' proper-support section module in more-etale.tex (0F4Y/0F76), with
etale-cohomology.tex 04FT for the support and 09Z9 for the fibre application. The three
search kinds above find no existing compact-section module. Its module also supplies the
canonical section-pullback and finite-coproduct/germ maps belonging to this calculation.

## Validation

Both Lean files compile cleanly through the prescribed `scompile.py` wrapper. The compact-section
module places its declarations under a module-wide `noncomputable section`; consequently the
primary declaration is written with the ordinary `def` keyword and the node's `lean.statement`
records the exact signature extracted from the file. This preserves the noncomputable definition
while matching the stage-2 preflight parser. The repaired packet has no statement dispute or
unresolved node fault.
