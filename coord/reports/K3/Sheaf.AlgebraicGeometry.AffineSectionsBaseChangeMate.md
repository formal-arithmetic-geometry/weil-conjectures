## What changed

Replaced the sorry in `AlgebraicGeometry.exists_affineSectionsBaseChangeMate` with a
complete Lean assembly proof. Its signature and existing public imports are unchanged.
The proof constructs the source isomorphism from an affine extension comparison and
the inverse sections/pushforward comparison, proves its unit equation by naturality,
and transposes the desired identity under the extension/restriction adjunction.
For an arbitrary m, its pullback adjunct n satisfies unit;pushforward(n)=m.
Naturality of d and c extends the base-change unit square to the required identity.
The chosen a and d precede the L and m binders.

Added three modules, one public statement per module:

- `Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons`: proved the six
  normalized sections comparisons from existing direct-image/global-sections
  K-injective acyclicity, exact scalar restriction, and right-derived uniqueness.
  Its local helpers are proved. The exact-postcomposition and composite-unit
  helpers are reused from AffineSectionsPushforwardNormalization through a
  proof-only `import all`; their duplicate declarations have been removed.
  The scalar maps are restriction-of-scalars constructions acting identically
  on sections.
- `Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit`: isolates the affine-only
  extension isomorphism and its adjunction unit equation, parent step 2.
- `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare`: isolates parent
  step 3 at the canonical pullback unit. It is an equality over R, requires no
  quasi-coherence, and constructs no isomorphism or arbitrary-m mate.

The latter two are the remaining obligations. Their combination and the extension
from the unit case to arbitrary m are proved in Lean, rather than moved to a helper.
Updated the parent's proof, proof_deps and proof_origin to describe this assembly.
No definitions, existing theorem signatures, targets, other held modules, or unit
records were changed. `sk-thm-picard-duality` has no realized node of this item;
the parent route through the affine case of finite duality is retained.

Validation: all four modules compile together in import order through lcompile.py,
without warnings. The delivery dry run is the final validation. Source text was read
from Stacks cohomology.tex and perfect.tex, downloaded into the sandbox scratchpad;
in particular cohomology's lemma-derived-pushforward-composition and
remark-base-change, and perfect's lemma-quasi-coherence-pullback were checked.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_affineSectionsBaseChangeMate`
(node `lem-pc-affine-sections-base-change-mate`). Its body has no sorry.

Also proved the new theorem
`AlgebraicGeometry.exists_affineSectionsCompositionComparisons`
(node `lem-pc-affine-sections-composition-comparisons`), including the three
right-derived-unit equations. Its local helpers deriveSectionsComparison, underivedSectionsComparison, and
affineSectionsAcyclic have complete proofs. The two general derived-functor
helpers are imported from the existing normalization module, not redeclared.

Added exactly two holes, each in its own new module:

- `AlgebraicGeometry.exists_affineExtensionSectionsUnit`
  (`lem-pc-affine-extension-sections-unit`), exactly `:= by sorry`.
- `AlgebraicGeometry.affineSectionsBaseChange_unit_square`
  (`lem-pc-affine-sections-base-change-unit-square`), exactly `:= by sorry`.

This is a decomposition of one upper hole into two strictly smaller obligations,
with the sections-composition step and the final categorical assembly proved.
It is not a sorry-free proof of the whole dependency closure; the direct-image
acyclicity and other imported existing declarations retain their existing status.
Holes closed: 1 original. Holes added: 2. Net for this decomposition: -1,
before any separate reach/pruning calculation by the maintainer.

Edge cases checked before stating the obligations: the zero complex makes both
unit identities zero identities; identity g recovers the usual adjunction unit
and its triangle identity; identity f reduces to the affine comparison.
Nonflat base change, for example Z to Z/2, requires derived extension and is not
replaced with ordinary tensor: no Tor vanishing or base-change invertibility is
assumed. The unit square is formal for arbitrary E, whereas only the affine
extension comparison uses the quasi-coherence hypothesis. None of these statements
adds qcqs, boundedness, perfectness, or flatness. These checks are mathematical
edge-case checks; the entire general assembly is checked by the Lean compiler.

## No longer needed

Removed the duplicate local declarations `exactComp_unit_isIso` and
`composite_isRightDerived_of_acyclic` from the composition-comparisons module.
Replaced its direct import of DirectImageGlobalSectionsKInjectiveAcyclic with
`import all Sheaf.AlgebraicGeometry.AffineSectionsPushforwardNormalization`.
The acyclicity node remains needed and is available through that import.


Removed the direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` and removed
`lem-pc-ringed-spaces-derived-direct-image-composition` from this item's proof route.
The sections-composition construction instead uses
`lem-pc-direct-image-global-sections-kinjective-acyclic` plus abstract derived
uniqueness. The base-change unit-square obligation uses the fixed canonical
pullback-composition and adjunction data already defining the base-change map.
No replacement import of the pruned direct-image-composition module occurs in
the three new modules. This is local pruning; it does not assert that no other
target route reaches that module.

Removed the parent's direct imports of
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, but both remain needed
by the affine extension obligation and are imported there. Their nodes are
therefore not pruned. The old proof dependencies
`def-pc-global-derived-rhom`, `def-pc-derived-base-change-map`, and
`def-pc-affine-global-hom-base-change-map` supply the unchanged statement data
and remain available through the unchanged public import; they are not pruned.

## Where the brief, the DAG or earlier work was wrong

Return point 1 repaired: the previous delivery duplicated two private theorems
already stated in AffineSectionsPushforwardNormalization. Their private status
does not require duplication: Lean module `import all` exposes them for local
proof use. Both copies are removed and the existing theorems are applied.
No existing library module or signature was changed. The composition node now
records the normalization dependency. The prior second reading below predates
this repair; its claim that local copies were necessary was incorrect.


No false statement or interface correction was found. The old proof plan's
named dependencies do not directly state the normalized affine adjunction-unit
compatibility or the sections of the base-change unit square. Those two gaps
are now explicit independent obligations, rather than an unstructured sorry.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
LeanFinder returned underived affine adjunctions, Loogle supplied the adjunction
unit/naturality API used by the assembly, and Mathlib grep found no exact
normalized affine-sections mate. Project and DAG searches found no existing
statement of either new obligation. Blueprint searches for affine sections
composition, affine extension sections, and base change unit found no duplicate.
The blueprint ancestor tool cannot follow created.item when it is a module name;
the new nodes preserve the parent's explicit ancestor `lem-sc-finite-duality`
and extend its via chain with the parent node instead.

## New nodes

`lem-pc-affine-sections-composition-comparisons` records the proved composition
step and its actual dependency on K-injective acyclicity. It is a construction
of right-derived composition comparisons, not a base-change mate theorem.

`lem-pc-affine-extension-sections-unit` records the affine-only K-flat/tilde
comparison with its fixed adjunction unit. It has no f, E on X, fibre product,
base-change map, supplied c, or arbitrary m.

`lem-pc-affine-sections-base-change-unit-square` records the canonical unit
identity for sheaf base change after normalized sections. It has no extension
isomorphism and no quasi-coherence assumption, and only the unit case rather
than a family indexed by m. The actual passage to arbitrary m is in the parent.

All three nodes have source places, complete proof steps, statement and proof
dependencies, the performed three search kinds (including the unavailable
LeanSearch result), and verbatim Lean statement records. There are no change
records because no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. Interface check: PASS. Read the diff against the repository module and compared
   the complete existing theorem signature byte for byte: identical. Only its body,
   proof imports, and local elaboration options changed. The three other modules
   are new. No existing definition, public import, target, or foreign held module
   changes, and no change record is required.
2. Proof check: PASS. Independently compiled all four files in import order using
   lcompile.py, without errors or warnings. The parent and composition comparison
   have no sorry; exactly the two reported public theorems remain `:= by sorry`.
   No definition is added, and there is no axiom, unsafe, opaque, extern,
   implemented_by, explicit sorryAx, or kernel-check bypass. The existential
   witnesses are eliminated inside theorem proofs, not used to define data from
   arbitrary unproved existence. Scratch copies with #print axioms check the four
   public theorems; the delivery probe also checks the private helpers.
3. Split statements: PASS as a decomposition, not a closed dependency proof.
   Read both full signatures and source/proof docstrings against Stacks
   perfect.tex lemma-affine-compare-bounded and lemma-quasi-coherence-pullback,
   and cohomology.tex remark-base-change and lemma-derived-pushforward-composition.
   The extension statement concerns one affine pullback with QCoh input and its
   unit, without f, a base-change square, or arbitrary m. The square statement is
   the canonical-unit identity over R, without an extension isomorphism or QCoh
   assumption. The parent proves transport of the affine unit, transposition,
   naturality, and the extension from the canonical unit to every m. Neither hole
   restates the parent. Checked zero complexes, identity maps, and nonflat base
   change: derived extension is essential, and no Tor vanishing is assumed.
   Independent project searches included DerivedBaseChangeUnitCompatibility and
   AffineSectionsPushforwardNormalization; neither states the remaining result.
   New-word Mathlib searches for the unit of an exchange mate found mateEquiv_square
   and leftAdjointUniq unit equations, useful abstract tools but not either full
   normalized sheaf statement. No hole can be closed merely by applying them:
   the affine derived comparison and normalized sections transport remain needed.
4. Route and pruning: PASS. Read the composition comparison's actual construction:
   identity restriction-of-scalars maps, K-injective sections acyclicity, and
   right-derived uniqueness. The upstream normalization helpers are private, so
   their local proved adaptations do not duplicate an accessible public lemma.
   All parent proof imports are used; public imports supply statement notation
   and definitions. The extension module retains the two imports for its open
   planned proof. Compared every old proof dependency with the new route:
   direct-image composition is removed locally; affine equivalence and affine
   pullback remain through the extension obligation; the three old definition
   nodes remain through the unchanged public statement-data import. No global
   pruning claim is made. Read sk-thm-picard-duality.realized (empty statement and
   step lists); no realized unit step is bypassed, and the finite-duality affine
   ancestor and route remain.
5. DAG check: PASS. All four recorded Lean statements match their source text.
   The parent's proof steps describe the actual Lean assembly; proof_deps is the
   union of their uses. Checked each new node's source, statement dependencies,
   proof steps/dependencies, origin, searches, split status, creation record,
   blueprint ancestry, chapter/unit, and Lean record. The proved composition
   node records its acyclicity dependency; the two open nodes retain the precise
   proof obligations with source-based plans.

Second reading changes: added this independent review and additional recorded
searches. No Lean proof, signature, import, definition, or node repair was needed.
The count remains one original hole closed and two lower holes added (net -1).

Axiom results: exists_affineSectionsCompositionComparisons uses only propext,
Classical.choice, and Quot.sound. The parent and the two open unit theorems use
those same standard axioms plus sorryAx, as expected from the remaining holes.

## Second reading by K3

1. Interface: PASS. Independently read the repository/sandbox diff and compared
   the existing theorem signature byte for byte, including every hypothesis and
   the order of the existential and universal binders: unchanged. The public
   import is unchanged. The other three modules are new; no definition or target
   changes and no change record is needed.
2. Proof: PASS. Recompiled all four modules in dependency order with lcompile.py;
   all compile without warnings. The parent uses adjunction injectivity, unit
   naturality, and naturality of c and d to prove the arbitrary-m equality.
   The composition theorem constructs its comparisons by scalar restriction and
   right-derived uniqueness. Exactly the two reported public theorems contain
   sorry. No definitions or prohibited trust mechanisms were added. Existential
   witnesses are used inside theorem proofs, never to define arbitrary data.
   Independent scratch copies with #print axioms check all four public theorems;
   the delivery tool additionally probes every local declaration.
3. Split obligations: PASS as a decomposition. Read both complete signatures,
   docstrings, and nodes, and checked the source passages in perfect.tex
   (affine-compare-bounded, affine-K-flat, quasi-coherence-pullback) and
   cohomology.tex (derived-pushforward-composition, remark-base-change).
   The affine-only obligation has no f, base-change map, or arbitrary m. The
   unit-square obligation has no extension isomorphism or QCoh assumption.
   Neither restates the parent. Zero input and identity maps specialize to unit
   identities; nonflat Z to Z/2 still uses derived tensor, not ordinary tensor.
   New-word LeanFinder search for the unit equation of a commuting adjunction
   square returned unit_mateEquiv, mateEquiv_square and related abstract lemmas.
   Local Mathlib search also found unit_leftAdjointUniq_hom_app. These require
   the missing derived sections/adjunction identifications, so do not immediately
   close either obligation. Loogle's unqualified Adjunction.leftAdjointUniq query
   returned unknown identifier; local source search supplied the actual API.
   Read DerivedBaseChangeUnitCompatibility and searched the project's sections
   and unit declarations: no duplicate normalized obligation was found.
4. Route and pruning: PASS. The repaired composition proof reuses the existing
   private exactComp_unit_isIso and composite_isRightDerived_of_acyclic through
   a proof-only import all of AffineSectionsPushforwardNormalization; the old
   review's justification for copying them is superseded. All current parent
   proof imports are used, and new public imports provide signature data.
   Compared every old proof dependency: direct-image composition is pruned
   locally; affine equivalence and tilde/pullback remain in the extension plan;
   the old definition dependencies remain statement data through the unchanged
   public import. The report lists these distinctions. The unit's realized
   statement and steps lists are empty, and the finite-duality affine route is
   retained. No additional short proof or import pruning was established.
5. DAG: PASS. Programmatically compared all four lean.statement strings with
   the declaration signatures and checked proof_deps against the union of uses.
   The parent changes only proof, proof_deps and proof_origin. Read each new
   node's proof, origin, source, search records, creation, blueprint ancestry,
   chapter, unit and Lean record; the normalization-helper dependency now agrees
   with the actual composition proof.

Second reading changed only this review report and scratch axiom-check copies.
The previous helper-import repair is correct; no further Lean or node edits were
needed. One original hole closed, two lower holes added: a decomposition with
net -1, not a closed proof of the dependency closure.
