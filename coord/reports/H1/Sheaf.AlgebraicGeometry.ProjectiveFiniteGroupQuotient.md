## What changed

The original theorem `AlgebraicGeometry.exists_finiteGroup_quotient_of_quasiProjective`
now has a complete Lean proof combining two strictly smaller remaining theorems.
Its signature and every public import are unchanged. No other existing Lean module
or existing node was changed.

A new proved module, `Sheaf.AlgebraicGeometry.QuasiProjectiveTowerAmple`, implements
absolute ampleness in the tower. The private composition proof base changes the
second immersion, applies the closed Segre embedding, and reindexes its finite
coordinate type. The private immersion pullback proof chooses affine section loci
inside the coborder range and uses the existing tensor-power pullback theorem.
This replaces the relative ample twisting prerequisite with an explicit proof.

The two new remaining theorems are the invariant-affine quotient construction
(original Steps 2--7) and ampleness on a given admissible quotient (Steps 8--9).
Each is in its own module with a complete proof in words and its own DAG node.
The latter takes Q and q as inputs and asserts only an ample invertible module;
the former asserts no ampleness, quasi-projectivity, projectivity or integrality.
Neither is the original theorem under another name.

The main module proves the remaining assembly: the quotient topology is
Noetherian by continuous surjective descent, giving quasi-compactness of r;
the existing affine-base ample immersion and `ProjectiveSpace.liftBaseChange`
give a finite-space immersion over B; `UniversallyClosed.of_comp_surjective`
and the proper-immersion criterion give projectivity; sectionwise injectivity
and surjective irreducibility give integrality.

Validation: all four modules compiled via lcompile.py, with times 12.0, 10.8,
7.5 and 17.7 seconds in the first successful complete compile. Two split modules
subsequently had all unused proof imports removed; the delivery compile checks
the final files. Main signature comparison was identical after whitespace
normalization. No shared interface changed, so no consumer adaptation is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_finiteGroup_quotient_of_quasiProjective`
(lem-per-projective-finite-group-quotient).

Also proved the new theorem
`AlgebraicGeometry.exists_ample_of_quasiProjective_tower`
(lem-per-quasiprojective-tower-ample), and all eight private helpers across the
two proved modules. There is no sorry in either proved module.

Added exactly two holes, each the entire proof of a public named theorem:

- `AlgebraicGeometry.exists_finiteGroup_quotient_of_ample`
  (lem-per-ample-finite-group-quotient-construction).
- `AlgebraicGeometry.exists_ample_on_admissible_finiteGroup_quotient`
  (lem-per-ample-admissible-finite-group-quotient).

This is a decomposition, not an axiom-complete proof of the original theorem:
one original hole closed, two lower holes added, net minus one before import
closure accounting. The absolute ample step and the final embedding, projectivity
and integrality arguments are implemented, not moved into either hole. No data
is defined by choosing an arbitrary witness of either remaining existence theorem.
Existing imported statements may still depend on other library sorries.

## No longer needed

The relative ample twisting node `lem-sfb-relative-ample-absolute-twist` and module
`Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist` are bypassed by the proved
Segre composition and immersion pullback argument. The free relative projective
bundle comparison node `lem-trf-free-projective-bundle-base-change-space` and module
`Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace` are bypassed because
the live ample immersion theorem already lands in the canonical projective space.

The separate `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` wrapper
and its node `lem-kun-projective-implies-proper` are unnecessary for this proof:
the canonical source-library `IsHProjective.isProper` instance already proves
the needed implication. The standalone Proj-separatedness input
`lem-weil-pbc-projective-space-proj-separated` is also unnecessary here; the
canonical projective-space properness instance supplies separatedness directly.
No upstream declaration is withdrawn or altered.

Removed direct proof imports from the original module:

- `Mathlib.AlgebraicGeometry.Gluing`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.RingTheory.Adjoin.Tower`
- `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres`
- `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`
- `Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace`
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
- `Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist`
- `WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen`
- `WeilConjectures.AlgebraicGeometry.Ample`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`

Several removed direct imports remain mathematical dependencies of the two
remaining construction/norm lemmas, or are now used by the proved tower module.
Their nodes remain in those new nodes' proof plans: affine-groupoid orbit fibres,
invariant-affine shrinking, invariant-localization and gluing, Artin--Tate,
finite-principal-affine sections, orbit-tensor descent and affine-cap-section-open.
They are not claimed to be unused mathematics. The two split modules import only
what their statements need; their later proofs can import the planned lemmas.
Obsolete parent tool-use approvals were removed while preserving the order of
those still directly used. No module was withdrawn and no DAG node was deleted.

## Where the brief, the DAG or earlier work was wrong

The original Step 10 describes the ample-to-immersion theorem as landing in a
polynomial Proj and therefore asks for a separate relative-Proj comparison. Its
current Lean signature already lands in the canonical finite projective space.
`ProjectiveSpace.liftBaseChange` already proves that the induced lift is an
immersion; the separate graph and comparison construction is unnecessary.

The original Step 1 explicitly avoided assuming quasi-projective composition.
The present proof assumes no such prerequisite: it proves the required composition
inside the new tower module using the source's Segre embedding. The more elaborate
relative-twist argument can therefore be pruned without changing the unit route.
The unit's realized statements and steps remain unchanged.

Rydh arXiv:0708.3333v2, Theorem 4.4 and Proposition 4.7, was read online. WANTED:
`literature/rydh-existence-properties-geometric-quotients-0708.3333.pdf` locally,
as in the inherited source record. The two remaining proofs in words spell out
the invariant-affine construction and norm argument from original Steps 2--9.

Edge cases checked mathematically: empty V and empty invariant opens; trivial or
ineffective finite group actions; wild characteristic; zero rings and nilpotent
distinguished elements in the invariant-localization calculation; an arbitrary
non-quasi-compact invariant open. Integrality is only asserted under IsIntegral V,
so it makes no false assertion about the empty scheme. The norm lemma requires
neither normality nor properness, and the projectivity proof only activates when
p is H-projective. No statement dispute or target change was introduced.

## New nodes

`lem-per-quasiprojective-tower-ample`: a proved absolute ample-source theorem,
independent of any group or quotient. Its full proof is in
`Sheaf.AlgebraicGeometry.QuasiProjectiveTowerAmple`.

`lem-per-ample-finite-group-quotient-construction`: the remaining invariant-affine
scheme quotient construction from an ample source, including finite type and
arbitrary invariant-open restrictions, with no projectivity/ample conclusion.

`lem-per-ample-admissible-finite-group-quotient`: the remaining norm-ampleness
argument for a fixed admissible finite quotient, with no quotient-existence or
relative projective-space conclusion.

All three were searched in the DAG, the current blueprint and Mathlib. Search
records use actual msearch.py query logs. The similar field-quotient theorem has
an essential field-base hypothesis; the historical composition node and general
qc-immersion ample-pullback node have no current Lean declaration. No duplicate
public notion is introduced. There are no change records because no existing
statement, definition or public import was changed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
