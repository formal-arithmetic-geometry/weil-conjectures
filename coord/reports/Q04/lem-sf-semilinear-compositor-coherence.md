## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence` states
`AlgebraicGeometry.ProEtale.VaryingRing.semilinear_compositor_coherence`.
Its only theorem has proof `by sorry`. It introduces no definitions, no alternative
functors, no new DAG nodes and no dependency replacements. The original node statement
and all of its other fields remain unchanged.

### Objects and hypotheses

- Arbitrary commutative rings in an inverse sequence are
  `R : ℕ → CommRingCat.{u + 1}` and `φ : ∀ n : ℕ, R (n + 1) ⟶ R n`.
  There is no assumption on the ring maps, no fixed coefficient ring and no flatness,
  finiteness, cartesianness or boundedness restriction.
- The schemes are arbitrary `Scheme.{u}` and their maps are arbitrary morphisms.
  The existing sequence-site operations use site object universe `u + 1`, morphism
  universe `u`, and coefficient universe `u + 1`, without equating the site universes.
- The node's `P_f = D(f*_{bullet})` is **`G R φ f`** in the recorded dependency API.
  Its `S_f = Rf_{*,bullet}` is **`P R φ f`**. Its `J_j` is `J R φ j`.
  `Derived R φ X` is the recorded ordinary unbounded derived category of the actual
  semilinear systems. No replacement categories are introduced.
- Open statements have `IsOpenImmersion` instances. In the transported associativity
  clause `k,l,m` are independently named composites of the open maps, with equalities
  `efg,egh,ekh,efl`. Their open-immersion instances express the structures on those
  same composite maps, forced by those equalities and stability under composition.
  They impose no further geometric assumption and cover every such composite.

### Every conclusion clause

The conjunction has nine clauses, ordered as follows.

1. Inverse-image associativity: the forward `d_{g,f}` of the node is
   `(gComp R φ f g).inv`. The first side applies `G f` to `d_{h,g}`, then applies
   `d_{hg,f}`; the other applies `d_{g,f}` at `G h M`, then `d_{h,gf}`.
   This is exactly the first displayed equation, evaluated at arbitrary `M`.
2. Direct-image associativity: `c_{g,f}` is `(pComp R φ f g).hom`.
   The left side is `P h` applied to `c_{g,f}`, followed by `c_{h,gf}`.
   The right side applies `c_{h,g}` at `P f M`, followed by `c_{hg,f}`.
   This is the second displayed equation at arbitrary `M`.
3. Open associativity: `e_{b,a}` is `(jComp R φ a b).hom`.
   The third clause applies `J h` to `e_{g,f}` then `e_{h,gf}`, and equates this
   with `e_{h,g}` at `J f M` followed by `e_{hg,f}`. This is the displayed open equation.
4. Inverse-image source identity: `d_{f,1_X}`, transported along `Category.id_comp f`,
   is `gId X` evaluated at `G f M`.
5. Inverse-image target identity: `d_{1_Y,f}`, transported along `Category.comp_id f`,
   is `G f` applied to `gId Y` at `M`.
6. Direct-image source identity: `c_{f,1_X}`, transported along `Category.id_comp f`,
   is `P f` applied to `pId X` at `M`.
7. Direct-image target identity: `c_{1_Y,f}`, transported along `Category.comp_id f`,
   is `pId Y` evaluated at `P f M`.
8. Open source identity: `e_{f,1_X}`, transported along `Category.id_comp f`, is
   `J f` applied to `jId X` at `M`.
9. Open target identity: `e_{1_Y,f}`, transported along `Category.comp_id f`, is
   `jId Y` evaluated at `J f M`.

In each associativity clause, `k : X ⟶ Z`, `l : Y ⟶ T`, `m : X ⟶ T` are arbitrary
named composites, and `efg : f ≫ g = k`, `egh : g ≫ h = l`, `ekh : k ≫ h = m`,
`efl : f ≫ l = m` are independently supplied equalities. Each occurrence of a binary
compositor is followed by its appropriate `eqToIso (congrArg ... equality)`.
Thus the statement includes transport of both intermediate and total composites,
not only a fixed associativity proof. Taking `k = f ≫ g`, `l = g ≫ h`,
`m = f ≫ g ≫ h` and the appropriate reflexive/associativity equalities recovers the
three ordinary displayed equations. Further substitutions in the maps or transports
(including in the unit equations) follow by equality elimination; proof irrelevance
identifies independently supplied equality proofs. The open transport uses `congrArg`
on the subtype `{a // IsOpenImmersion a}`, passing `a.property` explicitly to `@J`.
This is ordinary equality transport, not a new open-extension comparison.

The equations are at every derived object `M`. By natural-transformation
extensionality this is the stated equality of natural transformations; the canonical
functor associators have identity components, so their components are implicit in
these objectwise equations. All compositors and identity maps come directly from the
specified dependency constructions. The theorem never compares or equates distinct
adjunction structures, units or counits.

### Dependencies used

Read `def-sp-varying-ring-operations` and its full source, especially:

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`:
  `AlgebraicGeometry.ProEtale.VaryingRing.Modules`, `Derived`, `G`, `P`, `J`,
  `moduleAdj`, `adj`, `moduleJAdj`, `jAdj`, `modulePComp`, `moduleGComp`, `gComp`,
  `pComp`, `modulePId`, `gId`, `pId`, `moduleJComp`, `jComp`, `jId`.
  `gComp` is the exact localization of `moduleGComp` and `pComp` is its
  `conjugateIsoEquiv` under the fixed `adj` and its composite. `jComp` localizes
  `moduleJComp`; `jId` is the specified open-adjunction identity comparison.
- `def-weil-pbc-adjunction-conjugate` is the Mathlib leaf
  `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.conjugateEquiv`, with
  `conjugateEquiv_comp`, `conjugateEquiv_id`, `conjugateIsoEquiv` and
  `unit_conjugateEquiv_symm`. These are the node's existing Mathlib interface.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration.
  Use `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.IsOpenImmersion` as prescribed;
  they are already available through the operations module.

All recorded proof-dependency modules are imported, non-publicly:

- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift` and its universal property.
- `def-weil-pbc-composite-adjunction`: `Mathlib.CategoryTheory.Adjunction.Basic`,
  `CategoryTheory.Adjunction.comp`, `comp_unit_app`, `comp_counit_app`, `Adjunction.id`;
  the module is already imported through `CompositionIso` and `Mates`.
- `lem-trf-adjoint-composition-coherence`:
  `Mathlib.CategoryTheory.Adjunction.CompositionIso`,
  `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`.
- `lem-weil-pbc-conjugate-iso-unit-equation`:
  `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.unit_conjugateEquiv_symm`.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.
- `lem-weil-pbc-localization-universal-property`:
  `Mathlib.CategoryTheory.Localization.Predicate`, `CategoryTheory.Localization.lift`,
  `liftNatTrans`, `natTrans_ext`, `fullyFaithfulWhiskeringLeft`.
- `lem-weil-pbc-mate-pasting`: `Mathlib.CategoryTheory.Adjunction.Mates`,
  `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp`, `conjugateEquiv_id`.

The theorem docstring contains all eight natural-language proof steps from the node:
section restrictions and fibre-product uniqueness; ordinary adjoint associativity;
the two unit equations; exact localization; conjugation to direct image; ordinary
open adjoint associativity and units; exact open localization; equality elimination.

### Edge cases and source check

Checked the identity-map specializations (including all three maps identity), the
empty scheme and empty open, zero rings, arbitrary/nonflat transitions (e.g. successive
quotients from ℤ/4 to ℤ/2), zero derived objects and genuinely unbounded complexes.
No binder excludes these cases. No properness hypothesis is present: `P` is defined
as total derived direct image for every scheme map.

Read Stacks `sites-cohomology.tex`, `lemma-derived-pullback-composition` (Tag 0D6D)
and `lemma-derived-pushforward-composition` (Tag 0D6E). They supply composition and
adjoint uniqueness; the section-normalized coherence is the agent-written refinement
identified in the node. Also read the current supplied blueprint snapshot's
`sec-six-functors/sk-thm-sf-package/fix-prop-coherence.md` and its proof: it requires
identity/composition coherence and preservation of the fixed units and counits.
No statement correction or disputed statement was needed.

### Search for existing declarations

The prescribed wrapper searches were run for this group and item:

- LeanFinder, query “Associativity and unit laws of normalized inverse image derived
  direct image and open extension compositors for semilinear sheaf systems”: eight
  hits, ordinary sheaf-of-modules/pullback or open-immersion component identities;
  none states the result on these derived semilinear categories.
- Loogle, query `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`: one exact hit
  for the generic categorical proof input. It assumes right-adjoint coherence and
  does not prove this node's geometric normalization or unit laws.
- Mathlib grep via wrapper, query
  `gComp.*assoc|pComp.*assoc|jComp.*assoc|mapDerivedCategoryCompIso`, subdirectory
  `CategoryTheory`: 25 hits, principally descent compositors; no matching theorem.
- LeanSearch, query “Normalized compositors for derived inverse image direct image
  and extension by zero of semilinear ring systems are associative and unital”:
  eight hits, including ordinary `SheafOfModules.pushforwardComp` and unrelated
  normalization/semilinear statements; no match.
- Project/source `rg` for `semilinear-compositor`, `gComp.*assoc`, `pComp.*assoc`,
  `jComp.*assoc`, `VaryingRing`; direct ID search in `lean/WeilConjectures`; and
  name/related-identity searches in `dag/lean_names_upstream.json`, `lean/Sheaf`
  and `lean/WeilConjectures`. The exact item/name has no existing declaration.
  A related `AlgebraicGeometry.ProEtale.SemilinearProperOpen.compositor_associativity`
  in `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` was read in full, including
  its functor/compositor definitions: it states three associativity clauses only,
  lacks the six unit clauses and uses its own `SemilinearProperOpen` interface.
  It is not the complete statement of this node. This module uses the explicitly
  recorded `VaryingRing` operations, without duplicating their definitions.

### Validation

The final module is checked using the prescribed `scompile.py` server wrapper.
Early elaboration errors in subtype equality transport were repaired by explicitly
specifying the subtype predicate, its endpoints, and the open-immersion proof passed
to `@J`. No global build, local Lean compile, tool change, or upstream source edit
was performed. The required `deliver2.py --no-push` preflight and final delivery
are performed after the compile passes. The maintainer supplies the independent review.

Validation interruption: after the explicit subtype endpoint repairs, the server ceased
providing a usable published library. Repeated `scompile.py` attempts fail before
compiling this delivery, while compiling the unrelated dependency
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, with
`error: unknown module prefix 'Mathlib'`; server confirmation says
`Live published library is unavailable`. Final clean compilation and preflight are
not claimed. The same prescribed `deliver2.py --no-push` is being tried to confirm
whether its compilation path is available. No compiler wrapper, server setting, or
published build was modified to bypass this failure.

### Resume validation (2026-10-21 UTC)

Retained the saved packet and first ran the prescribed
`deliver2.py Q04 lem-sf-semilinear-compositor-coherence --no-push`.
It exited 1 before checking this module: overlay dependency
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` reports
`error: unknown module prefix 'Mathlib'` at line 6. The search path contains only
the live project's build directory and Lean's toolchain library. Server confirmation
reports `Live published library is unavailable`.

Retried the saved module with the prescribed `scompile.py Q04
lem-sf-semilinear-compositor-coherence <saved module path>`; it exited 1 with the
same missing-Mathlib dependency error and server confirmation. This is not exit 124
or a compile-server queue timeout. Neither attempt reaches this theorem, so there is
no delivery-source diagnostic to repair. No source, node record, launcher tool,
published artifact, or server setting was changed. The packet remains in the sandbox;
clean compilation, preflight acceptance, and delivery are not claimed.

### Further resume validation (2026-10-21 04:13 UTC)

Retained the saved module and first ran the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before reaching
the delivered module. The overlay dependency
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`, line 6,
cannot import `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`: its
`.olean` is missing from the live Mathlib build. The wrapper's server
confirmation reports `Live published library is unavailable`.

An independent prescribed `scompile.py` invocation for the saved module
exited 1 with the identical missing artifact and server confirmation. Neither
failed invocation reached this theorem, and neither was a queue timeout.
No launcher script or published library was modified. No delivery was pushed.

The saved signature still matches `lean.statement` verbatim, every source line
is within 100 characters, `autoImplicit` is explicitly false, and the module
contains one named theorem with its expected `sorry`. Refreshed the node copy
from the current read-only node while retaining its saved `lean` record, so
concurrent upstream `lean_audit` changes are not reverted. Only `lean` differs
from the current node. Clean compilation and preflight remain unverified
because the published dependency artifact is unavailable.

### Saved-packet self-check (2026-10-21 UTC, final retry)

Retained the earlier packet and began with the prescribed `deliver2.py --no-push`.
Re-read the current item, its three statement-dependency records, the relevant
`VaryingRingOperations` signatures and docstrings, Mathlib's conjugation interface,
Stacks 0D6D/0D6E, and the current blueprint's `fix-prop-coherence` statement and proof.
The saved node still differs from the current node only in `lean`; no mathematical
statement, dependency, construction or hypothesis needed changing. The record's
signature matches the file verbatim, every line is at most 100 characters,
`autoImplicit` is false, and the sole postponed proof is the named theorem.
The objectwise equations match all three compositor equations and both unit laws
for each family, with the equality transports and open-immersion instances present.
Earlier validation failures above are historical; the final wrapper results determine
whether this retry compiles and delivers. Independent review remains the maintainer's.

Final retry result (2026-10-21 UTC): the required dry run exited 1 before compiling
this module. Its overlay first timed out compiling
`WeilConjectures.Algebra.Homology.HomComplexSectionsCochains` after 60 seconds;
server confirmation then failed in `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
at line 6 because the published object file
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
Retried the exact saved module using the prescribed `scompile.py`. That invocation
advanced past the earlier timeout, but exited 1 at the same missing object file in
`CoefficientHomRepresentativeEvaluation`; its current-server confirmation reproduced
the missing-artifact error. Neither wrapper reached the delivered theorem. This is
a missing published build artifact, not an unstated mathematical dependency, source
elaboration error in this packet, or the compile-server 'no answer' timeout.
No library, launcher tool, build output or server configuration was edited. Only this
sandbox report was updated. Clean compilation, preflight acceptance and delivery
remain unclaimed; the packet is preserved for the published build to be repaired.

### Resume check (2026-10-21 04:25 UTC)

Started with the retained packet and the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before checking
this theorem: `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, line 6,
imports `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, whose
published `.olean` does not exist. The wrapper's current-server confirmation
reproduced that missing-artifact error.

Ran the prescribed `scompile.py` independently on the saved module. It also
exited 1 at the identical import, and its current-server confirmation reproduced
the same error (0.4 seconds). Neither invocation timed out or reached the item.
There is no delivery-source diagnostic to repair; the failed artifact belongs to
the read-only published build, which this worker cannot rebuild or modify.

Checked the packet against the current read-only node: only `lean` differs.
The saved signature matches `lean.statement` verbatim, no line exceeds 100
characters, `autoImplicit` is false, and the file contains one named theorem
with `sorry`. No repair note exists for this item. Retained the module and node
unchanged; only this sandbox report was updated. Clean compilation, preflight
acceptance and delivery remain unclaimed. No push was attempted.

### Saved-packet retry (2026-10-21 04:27 UTC)

Retained the saved packet and began with the prescribed `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before reaching
the item: overlay `Sheaf.Paper.RestrictionOfScalarsExact` could not import the
published `Sheaf/Paper/FiniteFieldFiber.olean`. Current-server confirmation
failed instead on the missing published object file
`WeilConjectures/RingTheory/FaithfullyFlat/FamilyDescent.olean` at the same
dependency's line 6.

Ran the prescribed `scompile.py` independently on the saved module. Both its
overlay check and current-server confirmation exited 1 because
`WeilConjectures/RingTheory/FaithfullyFlat/FamilyDescent.olean` does not exist
in the published live build. The confirmation took 0.5 seconds. Neither
invocation reached this theorem or returned the compile-server busy timeout.
This is a published-artifact/tooling failure; there is no item-source
diagnostic to repair. No tool, dependency source, or published artifact was
edited, and no push was attempted.

The saved node differs from the current read-only node only in `lean`. Its
recorded signature matches the file verbatim, the maximum line width is 93,
`autoImplicit` is false, and no repair note exists for this item. Retained the
module and node unchanged. Clean compilation, preflight acceptance, and
delivery remain unclaimed.

### Saved-packet retry (2026-10-21 04:33 UTC)

Began with the retained packet and the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. The wrapper advanced past
previous missing-artifact failures, but exited 1 before compiling this item:
`Sheaf.CategoryTheory.RingedSiteDualityMaps` has type mismatches at lines
795 and 828. At 795 its section-formula equality does not elaborate as the
required equality of composites with `homComplexπ`; at 828 the signed
evaluation formula does not elaborate as the expected formula using
`WeilConjectures.coefficientHomComponent`. No item-source diagnostic was emitted.

Retried the exact saved module independently with the prescribed `scompile.py`.
It exited 1 with the same two dependency errors. The prescribed `scompile.py
--source Sheaf.CategoryTheory.RingedSiteDualityMaps` confirms that the current
server source contains both failing proof terms. Neither failure is exit 124
or a compile-server busy timeout. Repairing unrelated upstream proof bodies
or changing shared compiler tooling is outside this worker's authorized packet;
no missing notion or unusable statement-dependency interface was identified.
No push was attempted.

Re-read the current node and its three statement-dependency records, the relevant
`VaryingRingOperations` constructions and normalization docstrings, Mathlib's
conjugation interface, Stacks 0D6D/0D6E and the current blueprint coherence unit.
The packet still differs from the current node only in `lean`; the signature
matches its record verbatim, maximum source width is 93, and `autoImplicit` is
false. The nine clauses cover the three transported associativity laws and
both unit laws for each family. No mathematical statement or module repair
was needed. Retained the node and module unchanged; only this sandbox report
was updated. Clean compilation, preflight acceptance and delivery remain unclaimed.

### Saved-packet retry (2026-10-21 05:46 UTC)

Started with the retained report and packet, then ran the required
`deliver2.py Q04 lem-sf-semilinear-compositor-coherence --no-push`.
It exited 1 before compiling the item: the current published dependency
`Sheaf.CategoryTheory.RingedSiteDualityMaps` has type mismatches at lines
795 and 828. Line 795 supplies a section equality that does not elaborate
as equality of composites with `homComplexπ`; line 828 supplies the signed
bidual evaluation formula where the goal uses `coefficientHomComponent`.

Independently ran the prescribed `scompile.py` on the saved item module.
It exited 1 with the same two upstream proof-body errors, before checking
this delivery. The prescribed `scompile.py --source
Sheaf.CategoryTheory.RingedSiteDualityMaps` confirms that the current server
source still contains both failing terms. These are concrete type errors,
not compile-server busy timeouts. The failing module is not an item statement
dependency requiring an interface repair; changing its shared proof bodies
or compiler machinery is outside this packet's authorized scope.

Re-read the item, its three statement-dependency records, the normalized
`VaryingRing` compositor and identity signatures and docstrings, Mathlib's
conjugation interface, Stacks 0D6D/0D6E, the current blueprint coherence
statement and proof, and the compact-object example's current upstream
replacement. No repair note exists for this item. The saved node differs
from the repository node only in `lean`; its recorded signature matches
verbatim, the maximum source width is 93, `autoImplicit` is false, and its
only postponed proof is the named theorem. The three associativity clauses
and six unit clauses retain the recorded canonical operations and transports.
Retained the module and node unchanged; only this sandbox report was updated.
No upstream source, launcher tool, or published artifact was modified, and
no push was attempted. Clean compilation, preflight acceptance, and delivery
remain unclaimed because the prescribed validation path fails upstream.

### Saved-packet retry (2026-10-21 05:49 UTC)

Started by reading the retained report and running the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before checking
this delivery, on upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` type
mismatches at lines 795 and 828 (21.7 seconds). The independent prescribed
`scompile.py` invocation reproduced both errors, also in 21.7 seconds. These
are not busy-server timeouts. The prescribed `scompile.py --source` successfully
returned the current server module; the validation path is failing on upstream
proof bodies rather than a missing notion or an unusable statement interface.

Retained the module and node. Compared the saved node with the current read-only
node: only `lean` differs. The recorded signature matches the source verbatim;
maximum line width is 93; `autoImplicit` is false. Re-read all three statement
dependency records and the actual `Modules`, `Derived`, `G`, `P`, `J`, compositor,
and identity definitions and docstrings. The nine clauses still express the three
transported associativity laws and six unit laws using the recorded operations.
No repair note exists for this item. No item-source diagnostic was produced;
removing the required operations import would remove the very objects being
stated. No shared dependency, launcher tool, or published artifact was modified.
Only this sandbox report was updated. Clean compilation, preflight acceptance,
and delivery remain unclaimed; no push was attempted.


### Saved-packet retry (2026-10-21 05:50 UTC)

Retained the saved packet and started with the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before checking
this item: upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` has type
mismatches at lines 795 and 828 (21.7 seconds). The independent prescribed
`scompile.py` invocation reproduced the same errors (21.7 seconds), also
before reaching this theorem. These are not busy-server timeouts. The prescribed
`scompile.py --source Sheaf.CategoryTheory.RingedSiteDualityMaps` returned the
current server source, confirming the failing upstream proof terms.

Line 795 supplies a section-formula equality where equality after composition
with `homComplexπ` is expected. Line 828 supplies `ringedSiteBidualDegree_eval`
where the goal uses `WeilConjectures.coefficientHomComponent`. These are upstream
proof-body failures, not an absent notion or an unusable statement-dependency
interface eligible for a packet repair. No shared source, artifact, or launcher
tool was changed, and no push was attempted.

Checked the retained packet against current sources: only `lean` differs from
the repository node; its signature matches the source verbatim; maximum line
width is 93; `autoImplicit` is false; the sole postponed proof is the named
theorem. Re-read the three statement-dependency records and the actual `Modules`,
`Derived`, `G`, `P`, `J`, compositor and identity declarations and docstrings.
No repair note exists for this item. Retained the module and node unchanged.
Clean compilation, preflight acceptance and delivery remain unclaimed because
the prescribed validation tools fail before checking the delivery.


### Saved-packet retry (2026-10-21 05:52 UTC)

Read the retained report and first ran the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before reaching
this theorem: upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` still has
type mismatches at lines 795 and 828 (21.7 seconds). The independent prescribed
`scompile.py` on the retained module reproduced both errors (21.7 seconds).
The prescribed `scompile.py --source Sheaf.CategoryTheory.RingedSiteDualityMaps`
successfully read the current server source. These are not busy-server timeouts.

At line 795 the section formula does not elaborate as the expected equality
of composites with `homComplexπ`; at line 828 the signed evaluation theorem
does not elaborate as the formula using `coefficientHomComponent`. These
failures are upstream proof bodies, rather than a missing notion or an unusable
recorded statement-dependency interface. No item-source diagnostic was produced.

Retained the node and module unchanged. Rechecked the three statement-dependency
records and the actual normalized compositor/identity signatures and docstrings.
Only `lean` differs from the current node; the signature before `:=` matches
`lean.statement` verbatim, maximum line width is 93, `autoImplicit` is false,
and the only postponed proof is the named theorem. No repair note exists for
this item. Only this sandbox report was updated. No shared source, launcher tool
or published artifact was modified; no push was attempted. Clean compilation,
preflight acceptance and delivery remain unclaimed.


### Saved-packet retry (2026-10-21 05:54 UTC)

Retained the saved packet and first ran the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before compiling
this theorem: upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` has type
mismatches at lines 795 and 829 (39.2 seconds). Independently ran the prescribed
`scompile.py` on the saved module; after the wrapper waited for a concurrent
compile, it exited 1 with the same two upstream errors (48.3 seconds). Neither
result was exit 124 or the compile-server busy timeout.

Read the current server source with the prescribed `scompile.py --source
Sheaf.CategoryTheory.RingedSiteDualityMaps`. At line 795 the section equality
fails to elaborate as the equality after composition with `homComplexπ`;
at line 829 the signed evaluation formula fails to elaborate for the locally
defined `β` and `coefficientHomComponent`. These are existing upstream proof-body
failures, not a missing notion or unusable recorded statement interface.
The required import path in the current read-only sources is
`VaryingRingOperations → SemilinearDerivedSections → SemilinearSystemsExistence
→ RingedInternalHomShiftOfUniverses → RingedSiteDualityMaps`. Removing the
operations import would remove the canonical objects required by this node.
No authorized item-source repair can fix these upstream proof bodies.

Re-read the item and all three statement-dependency records, the actual system
categories and canonical functor/compositor/identity definitions and docstrings,
and the Mathlib conjugation declarations. No repair note exists for the item.
Checked the packet against the current read-only node: only `lean` differs;
the saved signature matches `lean.statement` verbatim, maximum line width is 93,
`autoImplicit` is false, and the only postponed proof is the named theorem.
The three transported associativity clauses and six unit clauses still use the
recorded canonical operations. Retained the module and node unchanged; only this
sandbox report was updated. No shared source, published artifact or launcher tool
was modified. Clean compilation, preflight acceptance and delivery remain unclaimed;
no push was attempted.


### Saved-packet retry (2026-10-21 05:57 UTC)

Retained the saved packet and began with the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. Its local dependency check
hit the 60-second limit in `Sheaf.CategoryTheory.RingedSiteDualityMaps`, after
waiting for a concurrent compile. The wrapper then confirmed against current
server sources: it exited 1 with type mismatches at lines 795 and 828 in that
upstream module (20.5 seconds for the failing file). Nothing was pushed.

Independently ran the prescribed `scompile.py Q04
lem-sf-semilinear-compositor-coherence <saved module>`: exit 1, the identical
upstream type mismatches at lines 795 and 828 (21.7 seconds). These final
results are concrete compilation errors, not “no answer from the compile
server” or a busy-server exit 124. Both checks stop before this theorem.

Read current server source using `scompile.py --source
Sheaf.CategoryTheory.RingedSiteDualityMaps`. Its proof at line 795 uses a
sectionwise equality involving `coefficientHomComponent` where the goal uses
composition with `homComplexπ`; line 828 similarly fails to identify the
signed degree-evaluation formula with the formula for the local chain map β.
These are upstream proof-body failures. The required canonical operations
import this module through `SemilinearDerivedSections`,
`SemilinearSystemsExistence`, and `RingedInternalHomShiftOfUniverses`.
There is no missing notion or defective statement-dependency interface to
repair under §1(A)/(B); altering or shadowing the shared upstream proofs is
outside this packet's authorized scope.

Re-read the item, all three statement-dependency records, the actual
`Modules`, `Derived`, `G`, `P`, `J`, compositor and identity definitions and
docstrings, Mathlib's conjugation interface, Stacks 0D6D/0D6E and the current
blueprint's `fix-prop-coherence` statement. Checked all three transported
associativity equations and the six unit laws against the saved signature.
Only `lean` differs from the current node; the recorded signature matches
verbatim, maximum Lean line width is 93, `autoImplicit` is false, and there
is exactly one named theorem with `sorry`. No repair note exists for the item.
Retained the module and node unchanged; only this sandbox report was updated.
Clean compilation, preflight acceptance and delivery remain unclaimed.

### Saved-packet retry (2026-10-21 05:59 UTC)

Retained the saved packet and first ran the prescribed `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before checking
this item, on upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps` type
mismatches at lines 795 and 828 (21.7 seconds). Independently ran the prescribed
`scompile.py` on the retained module: exit 1, the same upstream errors
(21.7 seconds). Neither result is a busy-server timeout. Nothing was pushed.

Read the current server source with `scompile.py --source
Sheaf.CategoryTheory.RingedSiteDualityMaps`. Line 795 fails to identify the
section-formula equality with equality after composition with `homComplexπ`.
Line 828 fails to identify `ringedSiteBidualDegree_eval` with the formula using
`coefficientHomComponent` and the local chain map β. The required operations
import this module through `Sheaf.Paper.SemilinearDerivedSections`,
`Sheaf.Paper.SemilinearSystemsExistence`, and
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`. These are upstream
proof-body errors, not a missing notion or an unusable statement-dependency
interface. Repairing shared proof bodies is outside this packet's scope.

Rechecked the item and all three statement-dependency records, canonical
functor/compositor/identity signatures and docstrings, Mathlib conjugation,
Stacks 0D6D/0D6E, and the current blueprint coherence statement. No repair note
exists for the item. Only `lean` differs from the current repository node;
the signature matches its record verbatim, maximum line width is 93,
`autoImplicit` is false, and the only postponed proof is the named theorem.
Retained the module and node unchanged. Only this sandbox report was updated;
no shared source, published artifact or launcher tool was modified. Clean
compilation, preflight acceptance and delivery remain unclaimed.

### Saved-packet retry (2026-10-21 06:01 UTC)

Read the retained report and first ran the required `deliver2.py Q04
lem-sf-semilinear-compositor-coherence --no-push`. It exited 1 before checking
this delivery, with upstream `Sheaf.CategoryTheory.RingedSiteDualityMaps`
type mismatches at lines 795 and 828 (21.7 seconds). Independently ran the
prescribed `scompile.py` on the saved module: exit 1, the same two upstream
errors (21.7 seconds). Neither result was a busy-server timeout. No push was
attempted.

Read the current upstream source using `scompile.py --source`. Line 795
supplies the sectionwise formula where the goal is an equality of composites
with `homComplexπ`; line 828 supplies `ringedSiteBidualDegree_eval` where the
goal uses `coefficientHomComponent` and the local chain map β. The canonical
operations' existing import path reaches this module through
`SemilinearDerivedSections`, `SemilinearSystemsExistence`, and
`RingedInternalHomShiftOfUniverses`. These are upstream proof-body errors,
not a missing notion or unusable recorded statement-dependency interface.
No delivery-source diagnostic was produced, and the authorized packet does
not include repairs of these unrelated shared proof bodies.

Rechecked all three statement-dependency records and the actual `Modules`,
`Derived`, `G`, `P`, `J`, compositor and identity signatures and docstrings.
Only `lean` differs from the current repository node; its signature matches
the source verbatim, maximum line width is 93, `autoImplicit` is false, and
there is one named theorem with `sorry`. No repair note exists for this item.
Retained the module and node unchanged; updated only this sandbox report.
No shared source, published artifact or launcher script was modified.
Clean compilation, preflight acceptance and delivery remain unclaimed.

### Successful saved-packet validation (2026-10-21 06:07 UTC)

The required first `deliver2.py Q04 lem-sf-semilinear-compositor-coherence
--no-push` now passes: `OK (dry run): commit 6c2077b957f passes the preflight
and compiles; nothing pushed`. The wrapper confirmed against current server
sources after its initial dependency compile timed out. The earlier upstream
errors no longer prevent compilation. The module and node were retained unchanged.

## Second reading by Q04

This is the resumed worker's self-check of the saved packet; the maintainer's
independent review remains separate. Opened the current node, all three statement
dependencies, their declarations and docstrings, and the entire delivered theorem.
The ring sequence and transition maps are arbitrary. `G`, `P`, and `J` are exactly
the dependency's inverse image, total direct image, and open extension; the node's
letters `P` and `S` correspond respectively to the API's `G` and `P`.
The first three conjuncts match the three associativity equations, using
`gComp.inv`, `pComp.hom`, and `jComp.hom` respectively. The named composites and
four supplied equalities render arbitrary intermediate and total transport.
The last six conjuncts match both normalized identity laws for each operation,
with `gId`, `pId`, and `jId`; open-immersion structures on named composites follow
from their defining equalities and add no geometric restriction.

Checked the identity and empty-open cases, zero rings and derived objects,
nonflat transition maps, and unbounded complexes: none is excluded. Read Stacks
0D6D/0D6E and the current blueprint's `fix-prop-coherence` statement and proof.
Found no mismatch requiring a statement or module change. A mechanical comparison
confirms that only `lean` differs from the current node, the recorded signature
matches the file verbatim, every line has at most 93 characters, `autoImplicit`
is false, and the only postponed proof is the single named theorem's `sorry`.
No repair note exists for this item. Final delivery is through `deliver2.py`.
