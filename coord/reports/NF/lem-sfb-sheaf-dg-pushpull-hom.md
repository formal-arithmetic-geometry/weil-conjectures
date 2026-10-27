## Worker report

Draft statement module: `Sheaf.CategoryTheory.SheafDgPushpullHom`, namespace
`CategoryTheory.SheafDg.Pushpull`. No theorem is proved; every theorem has `sorry`
and a source/proof docstring. Definitions contain real data, or take the unique
structure/map specified by a named universal-property theorem. The source node's
statement and other fields are unchanged; only `lean` is attached.

Current validation status: the construction through `push` compiled cleanly using
`scompile.py` (12.3 seconds). Compilation of the completed draft stopped before
checking this file: the server could not prepare the dependency overlay, reporting
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` followed by
`resource exhausted (error code: 28, no space left on device)`. The same failure
occurred on the next retry. Earlier invocations also reported disk exhaustion in
the server's local compiler, but their server-confirmation fallback succeeded.
The final Hom/adjunction/base-change additions remain unverified. Nothing is pushed.
The prescribed deliver2.py --no-push dry run independently reproduced the same
overlay disk-space failure and printed COMPILE FAILED on the server, nothing pushed.

Hypothesis and clause audit:

- A morphism of ringed topological spaces is `f : X ⟶ Z`, coefficient sheaves
  `S : Z.Sheaf CommRingCat` and `T : X.Sheaf CommRingCat`, and the unital ring-sheaf
  map `c : rings S ⟶ f_* (rings T)`. This is the adjoint form of the inverse-image
  coefficient map in the node. The common universe `u` is explicit throughout.
- The source and target dg algebras are the dependency's `Algebra S` and `Algebra T`.
  `AlgebraMap f c A B` has a coefficient-linear chain map `A.X ⟶ f_* B.X`, with
  homogeneous multiplication and unit equations. This is the adjoint form of φ,
  including compatibility with the coefficient map and differentials.
- Modules are exactly the dependency's `LeftModule`; signed maps use its
  `GradedLinear` and `GradedMap`. No second dg-module definition is introduced.
- `coefficientPull` and `coefficientPush` are Mathlib's actual module-sheaf adjoints.
  `pullComplex` and `pushComplex` apply them degreewise. `pullSection` is the unit
  section `1⊗n`, and the ordinary evaluation is their fixed counit.
- `leftBalance` is `(b,c,n) ↦ (bφ(c),n)` via the uniquely normalized `tensorLift`;
  `rightBalance` is `(b,c,n) ↦ (b,cn)`. `pullObj` is their actual coequalizer in
  B-modules, starting from the free B-module on the ordinary coefficient pullback
  of N. Scalar balancing identifies this with `B⊗_{f⁻¹C}f⁻¹N`. Thus its differential
  and action are the direct-sum total tensor differential and the first-factor
  action, inherited by the quotient. No arbitrary left adjoint replaces this object.
- `pushObj` has precisely the degreewise direct-image underlying complex and the
  unique sectionwise C-action through φ (`IsPushAction`). `pull` and `push` give
  the actual object and chain-map functors.
- `gradedSubgroup` is the subgroup of global homogeneous coefficient-sheaf maps
  satisfying the dependency's signed-linearity equation. `homDifferential` is
  Mathlib's δ restricted to that subgroup. `homComplex` is an integer cochain
  complex in `AddCommGrpCat`, not just a family of cohomology identifications.
- `existsUnique_homIso` asserts an isomorphism of these complexes, natural in both
  module variables (`HomNaturality`). `HomFormula` gives evaluation at `1⊗n` in
  the forward direction and `(-1)^(r p) b k̃(x)` for the inverse on arbitrary local
  coefficient-pullback sections. `adjunctCochain` is the ordinary degreewise adjunct
  k̃. HEq transports only the displayed equalities of integer degree expressions.
- `existsUnique_adjunction` asserts the degree-zero closed-map adjunction and
  specifies both its unit and counit in `AdjunctionFormula`: the unit is `1⊗n`,
  and the counit is B-action after the ordinary evaluation counit.
- `homotopy_compatible`, `pullHomotopy`, `pushHomotopy`, and `homotopy_adjunction`
  give the adjunction on the dependency's homotopy quotient categories. The unit
  and counit are explicitly the images of those before taking the quotient.
- `shifts_cones` asserts natural comparison isomorphisms for every signed shift
  and isomorphisms of the mapping cones for both functors, with the cone-inclusion
  and negative-connecting-projection diagrams. Its proof docstring records the
  signs `(-1)^(k|b|)` for shifts and `(-1)^|b|` for the shifted cone summand.
- `baseChangeMap` is the coefficient-pullback adjunct P(C)→B. Its being invertible
  says exactly that the given B and φ are the canonical scalar-base-change algebra,
  allowing any identified copy of that algebra. `scalarBaseChange` supplies a natural
  chain isomorphism F(N)≅P(N), the contraction and unit-insertion formulas on local
  generators (arbitrary coefficient scalars follow by T-linearity), and explicit
  equalities identifying both unit and counit with the ordinary module adjunction.
- `existsUnique_freeHomIso` states the identity-space, degree-zero coefficient
  specialization as `Hom_B(B⊗L,I) ≅ Hom(L,UI)` in complexes of abelian groups,
  natural in L and I and with the same forward and signed inverse formulas.
- No hypothesis of exactness, flatness, boundedness, nonemptiness, nonzero rings,
  nonzero modules, or characteristic restriction is present.

Dependencies used:

- `Sheaf.CategoryTheory.SheafDgModuleLocalization`: `Algebra`, `LeftModule`,
  `action`, `GradedLinear`, `GradedMap`, `homotopyRel`, `Homotopy`, `q`,
  `moduleOn`, `regular`, `shiftFunctor`, `cone`, `coneIn`, `coneConnecting`,
  `tensorSection`, and `actionSection`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullback`, `pushforward`, `pullbackPushforwardAdjunction`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`:
  `SheafOfModules.module_pushforward_isRightAdjoint_of_universes`, supplying actual
  existence instead of imposing an additional adjoint-existence assumption.
- `Mathlib.Topology.Sheaves.SheafCondition.Sites`: continuity of `Opens.map f`.
- The stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.Sites.InverseImageUnderlyingAdjunction`
  (`site_inverse_image_multimap_universal`),
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`
  (`moduleInverseImageAdjunction`),
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`tensor_bilinear_universal`), and `Mathlib.Topology.Sheaves.Functors`
  (inverse-image adjunction). Sheafification is already a transitive statement import.

Edge cases checked mathematically before writing: empty spaces and empty opens,
zero modules and the zero ring, identity map, degree zero, degree -1 homotopies,
odd shifts and odd algebra degrees, characteristic two, and unbounded complexes.
In the inverse formula the balancing exponents are r(p+q)=rp+rq. The total tensor
uses sums, while Hom uses all homogeneous component maps; nothing moves an infinite
sum through direct image. The ordinary-base-change criterion includes the identity
case and any isomorphic presentation, rather than a chosen syntactic equality only.

Searches actually run:

- msearch leanfinder: `Natural Hom complex adjunction pullback pushforward sheaves
  differential graded modules` returned eight hits, chiefly ordinary module-sheaf
  adjunctions (`SheafOfModules.pullbackPushforwardAdjunction` and its unit formulas).
  None states the signed dg Hom-complex adjunction.
- msearch loogle: `SheafOfModules.pullbackPushforwardAdjunction,
  CochainComplex.HomComplex` returned zero hits.
- msearch grep in Algebra/Homology: `HomComplex|homComplex|mapMon|mapMod` returned
  the ordinary cochain Hom-complex API and its homotopy/cohomology companions.
  These are reused; they do not impose dg-algebra linearity.
- rg in `lean/WeilConjectures` for the exact item id returned no match. Searches in
  both project roots for SheafDg and signed Hom names found the recorded dg-module
  dependency but no pullback/pushforward Hom-complex statement. Searches for
  mapMod, monoidal pullback and module-sheaf adjunctions were also inspected.

No source-based statement correction or new independent definition node is proposed.
The structures and canonical-map helpers here belong to the constructions explicitly
introduced by this statement. No mathematical statement dispute was identified.

Retry validation (2026-10-24): retained the saved packet and first reran the
required `deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom --no-push`. It exited 1
before checking this module, reporting `overlay
Sheaf.CategoryTheory.SheafDgModuleLocalization` and `resource exhausted (error
code: 28, no space left on device)` (22.0 seconds). A subsequent prescribed
`scompile.py` invocation on the saved module independently exited 1 with the
same dependency-overlay failure (22.0 seconds). No Lean diagnostic was reached,
no source was changed, and no delivery was pushed. The packet remains intact
for retry after server disk capacity is restored.

A second dry run after a pause again exited 1 in 22.0 seconds with the same
dependency-overlay disk-exhaustion error; nothing was pushed.

## Second reading by NF

I reread the current node copy and the complete module. The single hypothesis is the
recorded dg algebra map `φ : AlgebraMap f c A B`, whose `map`, multiplication, and unit
fields render the coefficient compatibility, chain-map condition, and algebra-map
clauses. The theorem's conclusion is rendered by `existsUnique_homIso`: it quantifies
exactly over left dg modules `N` and `M`, gives an isomorphism between the two signed
hom complexes, and conjoins `HomFormula` (the evaluation and signed extension formulas)
with `HomNaturality` (naturality in both module variables). The surrounding declarations
render the remaining clauses of the node: `existsUnique_adjunction` gives the degree-zero
unit/counit adjunction, `homotopy_adjunction` its homotopy quotient, `shifts_cones` the
shift and cone comparisons, `scalarBaseChange` the specified tensor contraction and
ordinary unit/counit normalization, and `existsUnique_freeHomIso` the identity-space
specialization. Every postponed result is a theorem with `by sorry`; all definitions
use actual constructions or a named unique-existence choice. I found no mismatch and
made no further statement change. The compile remains unverified solely because both
`scompile.py` and `deliver2.py --no-push` stop before Lean with the server overlay
`resource exhausted (error code: 28, no space left on device)` failure recorded above.

## Dispatcher retry validation (2026-10-24)

This retry retained the saved packet and began with the prescribed
`deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom --no-push`. It exited 1 after
22.0 seconds, before Lean checked the delivered module, with:

```text
COMPILE FAILED on the server, nothing pushed:
overlay Sheaf.CategoryTheory.SheafDgModuleLocalization
resource exhausted (error code: 28, no space left on device)
```

An independent invocation of the prescribed `scompile.py` on
`lean/Sheaf/CategoryTheory/SheafDgPushpullHom.lean` also exited 1 after
22.0 seconds with the identical dependency-overlay disk-space failure.
No Lean diagnostic was reached. The Lean module and node copy are retained
unchanged, and no delivery was pushed. This remains a tool/server resource
failure, rather than an elaboration error repairable in this packet.

## Current dispatcher retry (2026-10-24)

Started by inspecting this saved report and invoking the required
`deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom --no-push`. It exited 1 after
22.0 seconds, before checking the delivered module:

```text
COMPILE FAILED on the server, nothing pushed:
overlay Sheaf.CategoryTheory.SheafDgModuleLocalization
resource exhausted (error code: 28, no space left on device)
```

An independent `scompile.py NF lem-sfb-sheaf-dg-pushpull-hom` invocation on the
saved `SheafDgPushpullHom.lean` also exited 1 after 22.0 seconds with the same
overlay disk-space error. The saved file uses the required module-mode header.
No elaboration diagnostic was reached, so there is no source repair indicated
by either tool. The Lean module and node copy remain unchanged; nothing was
pushed. The server resource failure prevents the required validation and delivery.

## Final dispatcher retry (2026-10-24)

Retained the saved packet and first ran the required
`deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom --no-push`.
It exited 1 after 22.0 seconds with `COMPILE FAILED on the server, nothing pushed`,
while preparing `overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`:
`resource exhausted (error code: 28, no space left on device)`.
The independent prescribed `scompile.py NF lem-sfb-sheaf-dg-pushpull-hom
lean/Sheaf/CategoryTheory/SheafDgPushpullHom.lean` also exited 1 after
22.0 seconds with exactly the same overlay disk-exhaustion error.
Neither invocation reached a diagnostic about the delivered Lean module.
No source repair is indicated by these results. The saved module and node copy
remain unchanged; no delivery was pushed. Validation is blocked by the compile
server's dependency-overlay resource failure.

## Saved-packet retry (2026-10-24)

Retained the saved packet, inspected its report, and first ran the prescribed
`deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom --no-push`. It exited 1 after
22.0 seconds with `COMPILE FAILED on the server, nothing pushed`, while preparing
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`:
`resource exhausted (error code: 28, no space left on device)`.
The independent prescribed `scompile.py NF lem-sfb-sheaf-dg-pushpull-hom
lean/Sheaf/CategoryTheory/SheafDgPushpullHom.lean` also exited 1 after 22.0 seconds
with the identical dependency-overlay disk-exhaustion error. Neither invocation
reached Lean checking of the saved module. No packet source repair is indicated;
the module and node copy remain unchanged, and nothing was pushed. The server
resource failure prevents the required validation and delivery.

## Latest saved-packet validation (2026-10-24)

Inspected the saved report and first ran the required `deliver2.py NF
lem-sfb-sheaf-dg-pushpull-hom --no-push`. It exited 1 after 22.0 seconds,
before checking the module, with `COMPILE FAILED on the server, nothing pushed`:
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization` followed by
`resource exhausted (error code: 28, no space left on device)`.
The prescribed independent `scompile.py NF lem-sfb-sheaf-dg-pushpull-hom
lean/Sheaf/CategoryTheory/SheafDgPushpullHom.lean` also exited 1 after 22.0 seconds
with the identical dependency-overlay disk-space failure. Neither tool reached
Lean diagnostics for this packet. No source repair is indicated by this server
resource failure. The saved Lean module and node remain unchanged; nothing pushed.

## Current saved-packet check (2026-10-24)

Inspected the saved report and ran the required `deliver2.py NF
lem-sfb-sheaf-dg-pushpull-hom --no-push` first. It exited 1 after 22.0 seconds:
`COMPILE FAILED on the server, nothing pushed`, while preparing
`overlay Sheaf.CategoryTheory.SheafDgModuleLocalization`, with
`resource exhausted (error code: 28, no space left on device)`.
An independent prescribed `scompile.py` invocation on the saved module also
exited 1 after 22.0 seconds with the identical overlay disk-space failure.
Neither command reached Lean diagnostics for this module. The packet's Lean
and node files are retained unchanged; no delivery was pushed. Repair requires
restoring compile-server disk capacity, outside this worker's authorized sandbox.

## Saved-packet validation in this session (2026-10-24)

The required first dry run, `deliver2.py NF lem-sfb-sheaf-dg-pushpull-hom
--no-push`, exited 1 after 22.0 seconds with `COMPILE FAILED on the server,
nothing pushed`. The prescribed independent `scompile.py` invocation on the
saved module also exited 1 after 22.0 seconds. Both failed preparing `overlay
Sheaf.CategoryTheory.SheafDgModuleLocalization` with `resource exhausted (error
code: 28, no space left on device)`, before checking the delivered module.
No Lean diagnostic or source repair was reached. The Lean module and node copy
are retained unchanged. No push was attempted because validation cannot pass
until the compile server's dependency-overlay disk-space failure is repaired.

## Saved-packet retry, server validation (2026-10-24)

Inspected the retained report and ran the prescribed `deliver2.py NF
lem-sfb-sheaf-dg-pushpull-hom --no-push` first. It exited 1 after 22.0 seconds
with `COMPILE FAILED on the server, nothing pushed`. An independent prescribed
`scompile.py` invocation on the saved `SheafDgPushpullHom.lean` also exited 1
after 22.0 seconds. Both failed preparing `overlay
Sheaf.CategoryTheory.SheafDgModuleLocalization` with `resource exhausted (error
code: 28, no space left on device)`. Neither reached checking of the delivered
module. Its required module-mode header is present. The Lean and node files
remain unchanged; no push occurred. Restoring the compile server's disk capacity
is outside this worker's authorized sandbox and is required before validation.
