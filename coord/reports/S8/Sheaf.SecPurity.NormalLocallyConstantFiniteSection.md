## What changed

Repair of the reviewer-approved delivery a06011f4958: removed the inherited
`set_option warn.sorry false` command from the item module. The landing's source-only
hole scanner matches the option-name suffix as an unattributed hole; removing the
warning suppression fixes the reported `<unattributed:26:939>` finding. No proof,
statement, definition or dependency was changed in this repair. The retained packet
was compared with current sheaf-dag source; delivery rebases it on the current server
branch. The repaired packet passed a fresh server-only `lcompile.py --all` after the
interruption: the geometric lemma module compiled in 1.5 seconds and the item
compiled in 8.0 seconds (exit code 0). The source-only ledger reports no unattributed holes or
gate failures; the delivery command reruns its complete checks. Its first preflight
required a record for the file-level option removal. Added
`coord/changes/S8-normal-finite-section-hole-scanner.md`, documenting the option,
the three downstream consumers and their unchanged mathematical interfaces.

Replaced the sorry in
`AlgebraicGeometry.exists_finiteEtale_section_of_normal_locallyConstant` by a complete Lean
proof from the existing representability theorem and one new geometric statement. The
existing public signature, public imports, and unit route are unchanged. No source-library
file or existing definition changes.

The proof restricts the cover index to universe u+1, compares inverse-image restriction
with sectionwise restriction by uniqueness of left adjoints, and applies representability.
Joint surjectivity supplies a nonempty cover member. A residue-field affine test object and
its colimit leg show its universe enlargement is nonempty, hence the representing scheme
is nonempty. The new geometric lemma supplies a finite etale surjection in the original
universe and an arrow to the representing scheme. Evaluation of the inverse representing
isomorphism supplies the section. All these steps are Lean proofs, including the restriction
comparison and site-cover conversion.

The new module `Sheaf.AlgebraicGeometry.NormalGeometricCoverUniverseDescent` isolates the
scheme-theoretic step. Its statement has no sheaf, local constancy, or section hypotheses
or conclusions. It retains the existing component-finiteness route and adds the universe
transport now required by representability. Its complete proof in words explains affine
chart transport, component selection, small finite algebras, overlap transport and gluing.
The existing node's proof and dependencies match the implementation.

Both delivery modules compiled together with lcompile.py --all (9.4 and 16.6 seconds before
final documentation and unused-import cleanup); the delivery tool reruns final validation.
Additional scratch experiments compiled the affine lift/Spec isomorphism by the terminal
object colimit and the small model of a finite ULift A-algebra using Module.Finite.small.
They confirm the local ingredients but do not supply the missing global gluing argument.

## Proved and sorry left

Original module: one hole before, zero after.
Closed: `AlgebraicGeometry.exists_finiteEtale_section_of_normal_locallyConstant`, node
`lem-a1-normal-locally-constant-finite-section`.

Added: one hole, `AlgebraicGeometry.normalGeometricCover_universeDescent`, node
`lem-a1-normal-geometric-cover-universe-descent`, in its own new module. Its body is exactly
`by sorry`. There are no other retained or added holes and no holes in definitions.

This is a decomposition, not a net reduction in hole count: one upper hole closed and one
strictly geometric hole added. The remaining work is transporting the normal Noetherian
base properties across schemeUniverseLift and gluing small models of the selected finite
etale component. None of the existing declarations states those universe-transport facts.

## No longer needed

Removed the item's private import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and its
direct proof dependency `def-weil-pbc-site-comparison-morphism`. Etale implies weakly etale,
so `Scheme.ProEt.mk p` makes the selected scheme a site object directly. This does not
withdraw the comparison module, which representability still uses.

Replaced the item's direct private import
`Sheaf.AlgebraicGeometry.NormalGeometricCoverComponents` by
`Sheaf.AlgebraicGeometry.NormalGeometricCoverUniverseDescent`. The component node remains
needed through the new geometric node; it is not globally pruned. The statement-only new
module imports only the modules required for its signature; its future proof dependency
on the existing component theorem is recorded in its node.

No nodes or modules are withdrawn. No target-reachable mathematical dependency is claimed
to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The previous landing failure was caused by the warning-control option, not an
anonymous proof hole: the source ledger recognizes the word `sorry` after the dot
in that option name. The repaired item has no such command and no literal holes.
The new geometric module retains exactly its one named public theorem hole.

The old plan applies normalGeometricCoverComponents directly to the representative over
X. The current representability theorem instead returns a scheme Z in universe u+1 over
schemeUniverseLift X, and represents F on enlarged test objects. This is necessary for
arbitrarily large sheet sets, but prevents the planned direct application and returning
the chosen component as an object of the original pro-etale site. The extra geometric
universe-descent lemma addresses precisely this gap without shrinking arbitrary sheet sets
or changing the item's signature.

The old local-triviality API also differs: the item uses sheafPullback along the base-change
functor, while representability uses proEtaleSetRestriction. The proved private comparison
identifies these by the map/pullback adjunction, the Kan-extension adjunction, and the
sheafification isomorphism of a sheaf. Arbitrary cover index universes require
restrictIndexOfSmall before applying representability.

Joint surjectivity of a pro-etale cover is extracted from its fpqc-cover membership; there
is no applicable JointlySurjective instance for the pro-etale precoverage.

## New nodes

`lem-a1-normal-geometric-cover-universe-descent`, attached to
`AlgebraicGeometry.normalGeometricCover_universeDescent`. This is the geometric component
step of Bhatt--Scholze Lemma 7.4.10 with explicit finite-algebra size descent, using the
canonical affine-colimit scheme enlargement and Stacks affine gluing/finite morphisms.
The node inherits the item's chapter and unit and preserves the component argument.
Mathlib semantic, Loogle and source searches and a whole-blueprint universe search found
no duplicate. Smallness of finite algebras is available in Mathlib, but the scheme gluing
and property transport API is absent.

Edge cases checked: nonempty Z excludes the empty covering; X is connected and therefore
nonempty. Over Spec k a component is a finite separable extension, whose carrier is small.
An infinite disjoint union causes no problem because only one component is selected.
A proper open immersion generally fails the full valuative criterion, so it supplies no
counterexample. No finiteness of the sheet sets, the index set, or Z is imposed. The option-removal change record is
`coord/changes/S8-normal-finite-section-hole-scanner.md`. No existing statement or
definition changes, and there are no forced adaptations.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
