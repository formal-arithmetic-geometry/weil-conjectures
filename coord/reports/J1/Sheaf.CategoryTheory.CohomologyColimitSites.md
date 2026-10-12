## What changed

Proved `CategoryTheory.cohomology_colimit_of_sites` from two finite-stage criteria.
The signature and the two public imports are unchanged. The proof takes a representative
of a filtered group colimit element, uses eventual vanishing to show its kernel is zero,
and uses class descent to prove surjectivity. Mathlib then reflects this bijection as
an isomorphism. The source's dimension-shifting route is retained in the two new items;
there is no use of the original continuity theorem in their statements or proof plans.
The module docstring now describes the proof actually written. The parent's node records
the finite-stage reduction, and two new modules/nodes state its remaining parts.

Validation: the original module compiled before editing; both new modules and the
complete reduction compiled locally. The new statements were checked at degree zero,
for the zero system, and for a one-object identity diagram: descent becomes existence
of a representative, and eventual vanishing becomes zero-kernel detection. Neither
claim implies the other for a general group cocone (inclusion of a proper subgroup
satisfies detection but not existence; a quotient map satisfies existence but not
zero-kernel detection). Thus neither new statement is the original theorem renamed.
The dry-run delivery performs the final local/server compilation and static preflight.

## Proved and sorry left

Proved: `CategoryTheory.cohomology_colimit_of_sites` (one of one original sorries).
No direct sorry remains in the item's module. This is a reduction, not an unconditional
closure: it depends on the following two public theorems whose entire proofs are `by sorry`:

- `CategoryTheory.cohomology_colimit_sites_class_descent`, node
  `lem-weil-pbc-colimit-sites-class-descent`, module
  `Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent`.
- `CategoryTheory.cohomology_colimit_sites_eventual_vanishing`, node
  `lem-weil-pbc-colimit-sites-eventual-vanishing`, module
  `Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing`.

Each is a strict part of continuity, with its source and a complete natural-language
proof in the docstring and its matching node. Existing dependencies remain unchanged.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.CategoryTheory.ColimitSiteCechComplex`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Sheaf.CategoryTheory.SiteCechComplex`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`

Their arguments remain in the new helpers' proof plans. The new helpers retain the
five necessary proof imports; their direct `SiteCechComplex` import was removed because
`ColimitSiteCechComplex` publicly imports it. The corresponding nodes still matter
transitively; this delivery does not claim to remove their modules from target closure.
The original proof dependency `lem-weil-pbc-five-lemma` is unnecessary along this route:
the new plans use the two explicit right-exact-row element chases, and the final Lean
proof uses kernel detection and class lifting. All other original proof dependencies
are retained in the two new nodes. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

`ColimitSiteSections.colimitSite_sections_isIso` compares a diagram of sheaves already
on the colimit site with its sections there. It does not directly identify stage
sections of different sites with sections of their inverse images. The degree-zero
argument also needs the inner-colimit formula of Sites 0A35 and the reindexing argument
in 09YN. The new docstrings and node plans specify that missing identification;
no existing signature was changed. The injective-system theorem uses adjoint-transposed
transitions, so applying it requires transposing the original inverse-image maps.

The local repository has no `literature/stacks-project/sites-cohomology.tex`.
The source was read from the official Stacks pages for 09YP, 0739, and 09YN.
LeanSearch returned Internal Server Error; this is recorded as an unavailable search,
without a fabricated verdict. LeanFinder, Loogle, source grep, and blueprint searches
were available and supplied no existing finite-stage continuity lemmas.

## New nodes

`lem-weil-pbc-colimit-sites-class-descent` states that every target cohomology class has
a representative at a stage. Its proof follows 09YN in degree zero, then the surjectivity
chase in the 0739 right-exact diagram after the injective-system/acyclicity argument
of 09YP. It leaves uniqueness unstated. Module:
`lean/Sheaf/CategoryTheory/CohomologyColimitSitesClassDescent.lean`.

`lem-weil-pbc-colimit-sites-eventual-vanishing` states that a stage class mapping to zero
is killed by a later transition. Its proof follows finite-stage equality in degree zero,
then lifts a stage class through the cokernel system, subtracts a lifted injective-system
class, and uses lower-degree relation detection before applying the connecting map.
It leaves existence of lifts unstated. Module:
`lean/Sheaf/CategoryTheory/CohomologyColimitSitesEventualVanishing.lean`.

Both inherit chapter `sec-proper-base-change` and unit `sk-thm-p1`; their searches cover
LeanSearch (unavailable), LeanFinder and grep. There are no change records because
no existing statement or definition changed.

## Second reading by J1

1. Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are unchanged; only proof imports, proof text, and the two
   explicitly listed helper modules were added.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no forbidden
   declarations or hollow definitions. The only remaining `sorry`s are the two named
   split-off theorems, each documented and matched by a node.
3. Checked both split-off statements on degree-zero, zero-system, and identity-diagram
   cases. They are strict existence and detection halves and do not restate the parent
   theorem; searches found no existing library theorem with either statement.
4. The proof follows the finite-stage representative, eventual-kernel-vanishing, and
   class-descent route. Removed imports are recorded above, and the unit route and
   realized steps remain represented in the parent and helper nodes.
5. The helper node statements, Lean declarations, proof plans, sources, and dependency
   lists agree. No statement or definition was changed, so no change record is needed.

Changed during second reading: added this verification section only; no Lean code or DAG
content required repair.
