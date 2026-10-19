## Worker report

This repairs returned immutable head `2c8927ab94e7`. The retained packet was first dry-run
unchanged: it compiled and passed the mechanical preflight as commit `35488987e3`. Reading
its actual signature against the returned review confirmed that the substantive H3, H4,
H8 and H11 findings remained, so the Lean module and this report have been repaired.
The current shared node was used as the JSON base; only `lean` and `stmt_deps` change.
There is no change to the mathematical statement, proof, proof dependencies or unit.

The module `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` defines the two inline
notions `AlgebraicGeometry.IsEtaModification` and `AlgebraicGeometry.IsEtaNormal` and states
`AlgebraicGeometry.geometricallyReduced_etaNormal`. Its only postponed theorem is the item,
with proof `sorry`. No new definition node or dependency module is needed: the previously
landed `def-trf-multipointed-curve` and `def-trf-multipointed-curve-modification` supply the
pair definitions. They were added to the statement dependencies and imported through
`Sheaf.AlgebraicGeometry.MultipointedCurveModification`.

Source checked: [Temkin, Stable modification of relative curves](https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf),
§1.2 (printed p. 2), §3.1 and Proposition 3.5.2 (printed pp. 20--21). Proposition 3.5.2
is the eta-normality theorem for flat finitely presented morphisms with geometrically
reduced fibres; its proof begins with reducedness. The semistable curve and etale marking
are the instances described using §1.2. The file's theorem docstring now records all ten
proof steps of the DAG, including the named inputs and checks for their hypotheses.

The correspondence with every hypothesis and clause is as follows.

| Node clause | Lean rendering and checked meaning |
| --- | --- |
| Schemes S and Z, with p:Z → S | `{S Z : Scheme.{u}} (p : Z ⟶ S)`; `u` is explicitly declared. |
| Integral base | `[IsIntegral S]`; this supplies nonemptiness and domain stalks. |
| Normal base | `hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)`; together with integral stalk domains, this is precisely normality in the node. |
| Base quasi-compact and quasi-separated | `[CompactSpace S] [QuasiSeparatedSpace S]`; the affine-open characterizations give a finite affine cover and quasi-compact pairwise intersections. |
| Flat p | `[Flat p]`, the recorded affine-local property, equivalent to flat stalk maps. |
| Finitely presented p | `[LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]`; all three are required by the comparison clause of `def-sbc-locally-finite-presentation`. The latter two were absent in the returned module. |
| Reduced geometric fibres | `[GeometricallyReduced p]`, Mathlib's base-change-to-fields predicate, equivalent to reducedness after the algebraic closure of each residue field. It adds no perfectness or characteristic assumption. |
| Reduced Z | `IsReduced Z`. |
| Eta-normal Z over S | `IsEtaNormal p`, universally quantifying `X' : Scheme.{u}` and `f : X' ⟶ Z`; hypotheses `IsFinite f` and `IsEtaModification p f`, conclusion `IsIso f`. |
| Proper eta-modification | The first conjunct of `IsEtaModification p f` is `IsProper f`. |
| Isomorphism between schematically dense opens | `U : X.Opens`, `V : X'.Opens`, `e : V.toScheme ≅ U.toScheme`, both inclusions injective on sections over every ambient open, and `e.hom ≫ U.ι = V.ι ≫ f`. The two `∀ W, Function.Injective (...app W)` clauses are exactly injectivity of the structure-sheaf maps, including the repeated density clause in the node. |
| Isomorphism induced on the generic fibre | The two `IsPullback` squares are over `S.fromSpecStalk (genericPoint S)` into S, with target map p and source map `f ≫ p`. The isomorphism e commutes with both projections: `e.hom ≫ i = j' ≫ f` and `e.hom ≫ q = q'`. Thus e is the base change of f, by uniqueness of maps into the target pullback. The retained packet incorrectly used p in both squares; that is repaired. |
| Both members of every semistable multipointed curve | `∀ (C : MultipointedCurve S), C.IsSemistable → IsReduced C.X ∧ IsEtaNormal C.x ∧ IsReduced C.D ∧ IsEtaNormal C.d`. All four conclusions are present, with the same base S. |
| Multipointed curve and marking | The existing `MultipointedCurve` supplies X, D, x, d, i, `comm`, both flat/lfp/qc/qs records, fibrewise pure dimensions 1 and 0, and `closed : IsClosedImmersion i`. No second structure is declared. |
| Nodal geometric fibres | The existing `C.IsSemistable` says each point of the algebraic-closure fibre is smooth or `Orgogozo.IsOrdinaryDoublePoint`. This uses `AdicCompletion` at the maximal ideal and `Orgogozo.nodeRing`, namely the two-variable `MvPowerSeries` quotient by the product of the variables. |
| Nodal isomorphism over the specified field | `Orgogozo.IsOrdinaryDoublePoint` includes `∀ a : Ω, e (AdicCompletion.of ... (localScalar p x a)) = Ideal.Quotient.mk _ (MvPowerSeries.C a)`. The retained `Nonempty RingEquiv` lacked this condition; using the existing predicate restores it. |
| Etale marking and relative smooth locus | The last two conjuncts of `C.IsSemistable` are `Etale C.d` and `∀ e : C.D, C.i e ∈ C.x.smoothLocus`. |
| Empty marking, nonseparated or nonproper curve | The reused structure has no nonemptiness field for D, and no `IsSeparated C.x` or `IsProper C.x`. Its `QuasiSeparated` fields are part of finite presentation, not separatedness. |
| Compatible pair eta-modifications | The imported `MultipointedCurve.Hom` stores both maps and their equations over the base and marking. Its `Hom.IsEtaModification` requires properness of both maps, dense target opens and inverse-image opens, and invertibility of each canonical generic base-change map. |
| Stable modification | The imported `MultipointedCurve.Hom.IsStable` uses semistability of the source and tests every geometric fibre component represented by a closed immersion of the projective line over the same algebraically closed field. Its final implication forbids a singleton image when that component has at most two special points. The special set is exactly marking union nonsmooth points. The theorem requires no stable modification as an extra hypothesis. |
| Topological dimension convention | `MultipointedCurve` uses `Scheme.IsPureDimension` on fibres; the underlying component dimension is `topologicalKrullDim` in `WithBot ℕ∞`, the recorded definition. |

Dependency declarations were read at their recorded source modules, including their
signatures and docstrings. Mathlib dependencies reused are `IsIntegral` and `IsReduced`
(`Mathlib.AlgebraicGeometry.Properties`), `LocallyOfFinitePresentation`
(`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`), `Smooth`/`smoothLocus`
(`Mathlib.AlgebraicGeometry.Morphisms.Smooth`), `IsClosedImmersion` (`ClosedImmersion`),
`Etale` (`Etale`), `IsFinite`/`IsIntegralHom` (`Finite`/`Integral`), `Flat` (`Flat`),
`IsProper` (`Proper`), `pullback`
(`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`), `AdicCompletion`
(`Mathlib.RingTheory.AdicCompletion.Basic`, with its ring structure in `.Algebra`),
`MvPowerSeries` (`Mathlib.RingTheory.MvPowerSeries.Basic`), and `topologicalKrullDim`
(`Mathlib.Topology.KrullDimension`). The additional Mathlib `QuasiCompact` and
`QuasiSeparated` classes are the standard morphism predicates, read in their own modules.
The pair declaration is `AlgebraicGeometry.MultipointedCurve`
(`Sheaf.TraceFormula.MultipointedCurve`); the semistability, pair-modification and stability
declarations are in `Sheaf.AlgebraicGeometry.MultipointedCurveModification`. Its nodal
predicate and scalar equation are in `Sheaf.Paper.OrgogozoInductionData`.

The recorded stated proof dependencies are imported without `public`: depth-two Hartogs,
normal dense-open integral sections, torsion-free invertible sections, etale smoothness
and fibre dimension, flat-local depth, Serre's reducedness criterion, smooth normal-ring
ascent, and the upstream smooth-geometric-reducedness module. Their exact theorem names
are respectively `Scheme.isIso_restrictAdjunction_unit_of_depth_two`,
`Scheme.exists_integral_section_denseOpen`, `Scheme.Modules.injective_smul_sections_of_flat`,
`smooth_and_fibre_dimension_zero_of_etale`, `IsLocalRing.depth_eq_add_of_flat_local`,
`Ring.isReduced_iff_serreR_zero_and_serreS_one`, `RingHom.Smooth.isNormalRing`, and
`Smooth.geometricallyReduced` (AlgebraicGeometry prefixes where appropriate).
The smooth affine/ring-map comparison is available from the public smooth import.
The two new Temkin proof nodes (normal approximation and fibre-generic smoothness) have
no recorded Lean declarations in the read-only base, and are named in the full proof
plan, not imported as invented modules. They are proof inputs, not unstated notions needed
to type this statement. No omitted proof import closes a cycle.

Edge cases checked before finalizing: S cannot be empty, exactly because it is integral;
Z may be empty and has no domain/nonempty hypothesis. The marking D may be empty; the
pointwise marking conditions then are vacuous and reducedness remains meaningful. Empty
fibres are allowed because pure dimension is componentwise, not an equation forcing a
nonempty fibre. Nonseparated and nonproper curves are allowed. A field base has its generic
fibre equal to the whole family, so an eta-modification is already an isomorphism there.
The constant nodal family remains allowed: eta-normality does not assert normality of its
nodal fibres. Arbitrary characteristic is allowed. All schemes and the field-valued
geometric-fibre constructions live in the same explicit universe u, without independent
small test universes or an extra universe equality.

Searches retained from the earlier packet: msearch LeanSearch “Flat families with reduced
geometric fibres over a normal scheme are eta normal” found only flatness/reducedness
building blocks, not this theorem; LeanFinder for flat finitely presented geometrically
reduced families over normal integral bases found normalization declarations; Loogle
`"AlgebraicGeometry", "Normal"` found relative normalization; grep for eta-normality and
geometric reducedness found the latter's general APIs, not this proposition.
Searches repeated for this repair: msearch LeanFinder “A flat finitely presented morphism
with geometrically reduced fibres over a normal integral scheme is eta normal” returned
8 normalization hits; Loogle `"AlgebraicGeometry", "Normal"` returned 12 normalization
hits; msearch grep `eta.normal|IsEtaNormal|IsEtaModification` under AlgebraicGeometry had
0 hits. `rg` on the upstream WeilConjectures tree for these names and the exact item id
found no eta-normality declaration. `rg` on shared lean/Sheaf for
`MultipointedCurve|IsSemistable|IsOrdinaryDoublePoint` found the canonical structures above.
The same notions are already carried by the two landed definition nodes; no new node is
created and the second semistability definition has been removed. The two generic helpers
are for arbitrary schemes over S, whereas `MultipointedCurve.Hom.IsEtaModification` is
specifically for a compatible curve-and-marking pair; it cannot replace the first
eta-normality clause for arbitrary Z. The helpers are owned by this node's inline notions.

The first repaired module compiled through scompile.py in both sandbox mode
(17.0 seconds) and library mode (4.0 seconds), with no diagnostics. The final version also
makes schematic density explicitly sectionwise and is checked again by the final dry run. The expected single
`sorry` is the main theorem's proof. The signature in `lean.statement` is copied verbatim
from `theorem` to before `:=`; all three declarations are listed, each with a source place
and this node's blueprint tag. Every Lean line is at most 100 characters.

## Second reading by Q90

This is the dispatcher's required author self-check, performed by reopening the repaired
file beside the current node, not a claim to be an independent reviewer. No other agent
was started. The maintainer provides the independent reading after delivery.

H3: I compared the complete binder list with “normal integral qcqs base; p flat and
finitely presented; reduced geometric fibres”. Integral-domain stalks come from
`IsIntegral`, integral closedness from hS, and base qcqs from the two space instances.
I found the retained finite-presentation omission and added both `QuasiCompact p` and
`QuasiSeparated p`. Both are also already present in the reused pair's six finiteness
fields. I checked the conclusions individually: Z reduced, all finite eta-modifications
invertible, and the same two conclusions for C.X and C.D for every semistable C.
I also made schematic density literal: each open inclusion's map on sections over every
ambient open is injective. This matches the node and the existing pair interface, without
using Mathlib's quasi-coherent kernel predicate (whose sectionwise characterization assumes
quasi-compactness). No quasi-compactness condition is imposed on the chosen dense opens.
In the generic-fibre helper I found and corrected the second square's structural map:
it now uses `f ≫ p` and the projection to X', rather than another copy of p. The two
projection equalities force the fibre isomorphism to be the one induced by f.

H4: I opened `MultipointedCurveModification.lean` and `OrgogozoInductionData.lean` and traced
`C.IsSemistable` into `Orgogozo.IsOrdinaryDoublePoint`, including its scalar equation.
The returned private structure used an unrestricted ring isomorphism of completions.
It is deleted; the theorem now takes the existing C and `C.IsSemistable`. I also checked
that the inline pair-modification and stability definitions in the node are the imported
`Hom.IsEtaModification` and `Hom.IsStable`, including compatibility, schematic density,
canonical generic maps, projective-line scalar compatibility and the two-special-points
test. The two landed definition nodes are now explicit statement dependencies.

H8: I compared all ten proof steps in the node with the theorem docstring: generic
injection/reducedness; normal Noetherian approximation; the finite algebra and open
isomorphism locus; the two injections; normal smooth neighbourhoods; extending integral
sections; the depth bound; Hartogs and the finite affine description; nodal reducedness;
and the etale marking. All ten, with their named dependencies, are present. Both helper
definitions now have source places and the exact blueprint tag. The module lists its
main definitions and statement. The previous abbreviated proof paragraph is gone.

H11: The clause table above was checked against actual fields, not just names: in
particular finite presentation has three classes, the generic-fibre squares use different
source schemes, and nodal compatibility is an equation on every scalar. I checked the
empty total space, empty marking and fibres, field base, constant nodal family,
nonseparated curves, arbitrary characteristic and the explicit universe. I found no
remaining statement mismatch or statement dispute; the mathematical node needs no
correction. Definitions have actual Prop data and no `sorry`; the theorem alone has
`sorry`. The final dry run and push use deliver2.py, with no direct repository edits,
git mutations or global build.
