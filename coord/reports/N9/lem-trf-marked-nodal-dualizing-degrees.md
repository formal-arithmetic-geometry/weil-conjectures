## Worker report

This repairs immutable returned head `72aeedfb63a8`. The saved packet initially passed
`deliver2.py --no-push` (candidate `2e223f366b`), but the required mathematical self-check
reproduced the review's semantic failures. That packet was not pushed. Its two modules and
stable-modification wrapper have been replaced, rather than rebased unchanged.

The mathematical statement of the item is unchanged. The theorem remains postponed by
`sorry`; all definitions have actual data. The main module is now
`Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees`, in the AlgebraicGeometry topic.
The new definition module is `Sheaf.AlgebraicGeometry.NodalDualizingDatum`.

### Hypotheses and objects

- Integral Noetherian base: `(T : Scheme.{u}) [IsIntegral T] [IsNoetherian T]`.
- Target and source multipointed curves: `(C P : MultipointedCurve T)`, using the landed
  `AlgebraicGeometry.MultipointedCurve` from `Sheaf.TraceFormula.MultipointedCurve`.
  Its fields supply flatness, local finite presentation, quasi-compactness,
  quasi-separatedness (finite presentation), pure relative dimensions 1 and 0, and the
  actual marking closed immersion and commuting triangle. No separatedness or properness
  over T is added.
- The same generic point in all hypotheses: `η`, `hη : IsGenericPoint η Set.univ`,
  `Smooth (C.x.fiberToSpecResidueField η)` and
  `Etale (C.d.fiberToSpecResidueField η)`.
- The morphism is the landed `MultipointedCurve.Hom` from
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`, with its actual curve/marking
  maps over T and marking compatibility.
- Stability is `f.IsStable (T.fromSpecResidueField η)`. This expands properness on both
  maps, schematically dense open isomorphisms, isomorphisms on the actual generic fibre,
  semistability of P, and exclusion of contracted projective-line components with at
  most two special points. The erroneous `IsStable (𝟙 T)` and the unrelated stored eta
  are gone. The already landed modification node is now a direct statement dependency.

### Each conclusion

1. The existential `D : MarkedNodalDualizingDegreesData P` supplies an actual module
   `D.omega`. Its `dualizing : NodalDualizingDatum P.x D.omega` includes invertibility,
   the global fundamental-class morphism `Ω¹_{P.X/T} ⟶ D.omega`, a cover by regular affine
   curve presentations, and normalized local descriptions. There is no unconstrained
   `∃ F, omega ≅ F` clause.
2. `NodalCanonicalPresentation` has affine opens U,V, their actual structure ring map,
   a surjective polynomial quotient in `c+1` variables, an ordered regular sequence of
   length c, and equality of its generated ideal with the quotient kernel. Its `immersion`
   is `U.toSpecΓ ≫ Spec.map quotient`, not an arbitrary chart map.
3. `NodalDualizingDatum.local_ext` identifies the pushforward of the actual restriction
   of omega with `NodalCanonicalPresentation.ext`. The latter calls the recorded
   `AlgebraicGeometry.moduleSheafExt` in integer degree c = n-1, with arguments
   `i_*O_U` and the ambient structure module. The ordered coordinate volume form identifies
   that second argument with Ω^n of affine n-space over V. The standard derived category
   is passed explicitly; no new axiom, chosen Abelian structure or size restriction is used.
4. Local free-module isomorphism alone would permit an arbitrary twisted line. Therefore
   `NodalDualizingDatum.normalized` also requires, in EVERY regular presentation, a
   B-linear trivialization e satisfying
   `e(alpha(dq(a))) = q(det(d(f_1,...,f_c,a)/d(x_0,...,x_c)))` for every polynomial a.
   `jacobian` computes this determinant with `MvPolynomial.pderiv` and `Matrix.det`.
   This is the Koszul/determinant normalization of the fundamental class. It fixes the
   transition ratios and allows gluing over arbitrary overlaps without separatedness.
   `D.canonical` states the corresponding unique isomorphism commuting with the
   fundamental class to every other datum, so canonicality is an actual conclusion.
5. `D.cartier : IsEffectiveCartierCenter P.i` uses the real marking inclusion.
   `markedNodalLine P D.omega` is DEFINED to be
   `D.omega ⊗ₘ P.i.ker.toModulesᵛ`: the actual Cartier-ideal dual, not a fresh twist or
   arbitrary isomorphic line. `D.marked_invertible` asserts its invertibility.
6. `D.base_change` quantifies over EVERY `T' : Scheme.{u}` and `q : T' ⟶ T`, with no
   Noetherian, integral, reduced, flat or nonempty condition on T'. It gives a normalized
   dualizing datum on the actual tensor pullback of omega. The explicit generator equation
   says its fundamental class sends the pullback of `da` to `d(q^sharp a)` followed by
   the pulled-back class. It uses the existing canonical
   `Scheme.Hom.relativeDifferentialsPullbackGenerator`, not an arbitrary map. It also
   asserts Cartierness of the actual base-changed marking and an isomorphism of the
   tensor pullback of the marked line with the pulled-back omega tensored with the
   dual of that base-changed marking ideal. This is a genuine identification of the
   constructions, rather than automatic invertibility of pullback. Every module
   pullback in both files is `Scheme.Modules.tensorPullback`.
7. `D.normalization_degree` binds an algebraically closed field Ω and an actual geometric
   point `t : Spec Ω ⟶ T`. It binds an INTEGRAL scheme Z with a closed immersion j into
   `pullback P.x t`, requires its image to be an irreducible component, and requires
   `IsProper (j ≫ pullback.snd P.x t)`. This is exactly the proper reduced component
   of the structural geometric fibre, represented by its integral closed embedding.
   The integral structure supplies the reduced subscheme structure; the component-image
   requirement excludes arbitrary maps and empty schemes.
8. `markedNodalComponentDegree` uses `Z.normalization`, `Z.fromNormalization`, their
   actual composite to P.X, the actual tensor pullback of the marked line, and the
   recorded `Scheme.Modules.degree`. Its explicitly supplied Over structure is the
   composite to Spec Ω. `markedNodalComponentGenus` uses exactly the same field
   structure and the recorded `Scheme.arithmeticGenus`, which is `dim Ω H¹(O)`.
9. `markedNodalBranches` is the inverse image on Z.normalization of the union of the
   actual base-changed marking and the complement of the ambient fibre's smooth locus.
   Its finite-set assertion and `ncard` determine n_Z; there is no arbitrary integer
   binder. Thus a self-node contributes two distinct normalized preimages; an ambient
   boundary node contributes the preimage on this component; smooth markings contribute
   once. The equation is exactly `degree = 2*genus - 2 + ncard`.
10. Positivity is a separate conclusion of the theorem: for each geometric point
    `z : Spec Ω ⟶ C.X`, j embeds an integral component of the ACTUAL fibre
    `pullback f.curve z`, and `topologicalKrullDim Z = 1` is required. Degree is again
    computed on the canonical normalization. An integral closed immersion with
    irreducible-component image is the reduced closed component, equivalently the
    component of the reduction. Properness here follows from f being proper and is
    not an extra hypothesis. No positivity is asserted for arbitrary structural-fibre
    components, points, empty schemes or arbitrary maps into P.X.

### Dependency declarations actually used

The original statement dependencies retain their recorded interfaces: Mathlib's IsIntegral,
IsNoetherian, LocallyOfFinitePresentation, Flat, Smooth, Etale, IsClosedImmersion, IsProper,
pullback and topologicalKrullDim; the landed MultipointedCurve and Hom.IsStable;
upstream Scheme.Modules.IsInvertible (Modules.Invertible), IsEffectiveCartierCenter
(Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier), ker.toModules and its dual
(EffectiveCartier), Scheme.normalization/fromNormalization
(Mathlib.AlgebraicGeometry.Normalization), and degree/arithmeticGenus
(Cohomology.EulerChar). Regular sequences use Mathlib's RingTheory.Sequence.IsRegular.
The completed node condition and formal power series occur inside the imported semistability
predicate, through Orgogozo.IsOrdinaryDoublePoint; they are not redefined here.

The new datum uses Scheme.Hom.relativeDifferentials and relativeDifferentialsDerivation
(WeilConjectures.AlgebraicGeometry.Modules.Differentials), and moduleSheafExt
(Sheaf.AlgebraicGeometry.SheafExt). Canonical module pullback is the recorded
WeilConjectures.AlgebraicGeometry.TensorPullback. The additional landed dependency
`def-a1-relative-differentials-pullback-map` supplies the canonical tensor generator through
Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap. Each already stated proof
prerequisite's recorded module is imported without `public`, as the stage rule requires;
no theorem about an unstated prerequisite is assumed as an extra hypothesis.

### Edge cases and source reading

I opened Temkin's primary PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf,
printed pp. 2--3: multipointed and relative stability definitions; local regular-immersion
Ext/Koszul construction; nonseparated locality; arbitrary base change; Cartier marking;
normalization and the boundary in Theorem 1.1. The local literature path in the node is
absent on this machine, so this reading used the primary PDF.

Empty marking yields the untwisted line and an empty marking contribution. Empty boundary
sets have cardinal zero. Self-nodes count twice on normalization; nodes meeting a different
component count on their own branch. Empty Z is excluded by IsIntegral, not by a new
nonemptiness assumption. Identity modifications are admitted at the generic-point map;
an unmarked identity elliptic curve has structural degree zero, and its zero-dimensional
fibres over itself are excluded from positivity. Nontrivial exceptional modifications are
admitted. No field characteristic, base-change flatness, source separatedness or source
properness is imposed. Non-Noetherian and empty base changes are admitted; the local
presentation cover is vacuous on an empty source. The `c=0` smooth affine-line presentation
uses degree-zero Ext and a one-by-one derivative, rather than a negative Ext degree.

### Searches and checks

The retained search history found no exact theorem (LeanFinder, LeanSearch, Loogle and
Mathlib grep). This repair ran msearch.py LeanFinder with “relative canonical sheaf local
complete intersection fundamental class Jacobian determinant”; eight hits on Jacobians and
smooth presentations, no dualizing datum. Loogle query `"dualizing"` returned no hits.
LeanSearch query “relative dualizing line fundamental class complete intersection Jacobian
determinant” returned eight smooth-presentation Jacobian identities, no such line/datum.
Mathlib grep `dualizingSheaf|dualizingModule|NodalDualizingDatum` in AlgebraicGeometry
returned zero hits. rg in WeilConjectures and lean/Sheaf found the reused differential and
Ext APIs, modification predicates and canonical differential pullback generator.
`tools/blueprint_refs.py search 'relative dualizing'` found three etale coefficient-complex
nodes (different category), and the DAG search found the unstated theorem
lem-trf-flat-lci-canonical-adjunction, whose missing notion is defined here, without
postulating that theorem. `blueprint_refs.py ancestor` gave lem-trf-local-term-locality.

All variables and universes are explicit, with autoImplicit and relaxedAutoImplicit disabled.
The final record signatures are extracted verbatim from their respective files. The new
module has no postponed proof; the sole sorry is the item's named theorem. Its docstring
now gives all eight proof steps, including local codimension, canonical gluing, Cartier
base change, branch multiplicities, Euler degree, boundary and genus-zero cases.

## New nodes

`def-trf-nodal-dualizing-datum` defines the missing Jacobian-normalized adjunction datum,
including its local regular presentations, actual Ext modules and fundamental class.
Its module is `Sheaf.AlgebraicGeometry.NodalDualizingDatum`. No new stable-modification
node remains: the landed `def-trf-multipointed-curve-modification` already owns that notion.
The new definition is cited directly by the item, with the existing module-pullback and
canonical differential-generator definition nodes also added as direct dependencies.

## Dependency modules

None. Existing dependency declarations are used directly; no node's interface is replaced.
The stale copied dependency node from the retained packet was removed, since the actual
modification node and its module are now on the delivery base.

## Second reading by N9

I reread the informal item and both final modules after replacing the returned packet.
The hypothesis matching is the five entries above: same integral Noetherian T; existing
source and target multipointed curves; common generic point; generic smooth and etale
fibres; stable modification at fromSpecResidueField of that point. The ten conclusion
entries above match the actual definitions/fields, including the actual Ext arguments,
fundamental-class Jacobian normalization, unique normalized isomorphism, Cartier ideal
and marked tensor, arbitrary base change with its generator equation, proper integral
structural-fibre components, canonical normalization/degree/genus, derived branch count,
and dimension-one target-fibre positivity. This reading found and removed the old
whole-base isomorphism condition, tautological Ext and base-change fields, arbitrary nZ,
and arbitrary-map positivity. No node statement correction was necessary: these were
errors of the previous Lean rendering. All eight numbered return points are addressed
by the changes described above, including documentation, topic, pullback and prerequisite
reuse. Compiler/dry-run validation is recorded below after completion.

Validation: the authorized command
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N9 lem-trf-marked-nodal-dualizing-degrees lean/Sheaf/AlgebraicGeometry/NodalDualizingDatum.lean lean/Sheaf/AlgebraicGeometry/MarkedNodalDualizingDegrees.lean`
completed with exit 0 and no errors or warnings. Each sandbox and library-form file compiled
separately: helper 3.2/4.2 s; main 3.7/4.7 s. No global build, direct Git command or live
source mutation was used. The delivery wrapper performs the authorized rebase/bookkeeping.
