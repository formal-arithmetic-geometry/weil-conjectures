## What changed

Reduced the unchanged `AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_stalk_bijective`
to one section-level theorem on the affine basis. The original module now extends the basis
map using `TopCat.Sheaf.restrictHomEquivHom`, proves that the extension agrees with the unit
by sheaf morphism extensionality, proves stalk bijectivity from basiswise bijectivity using
germ representatives, and cancels the bijective stalk map of the sheafification unit.

Added `Sheaf.AlgebraicGeometry.RingSheafificationRestrictedStalks`, with a complete proof of
`AlgebraicGeometry.ringSheafification_restricted_stalk_bijective`. Forgetting rings commutes
with sheafification; finality of the opposite image functor on neighbourhoods identifies
restricted stalks with ambient stalks. The naturality square is proved on colimit legs.

Added `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison`, stating the remaining
natural affine section identifications, their bijectivity, and compatibility with the explicit
comparison. It asserts nothing about stalks. No signatures, definitions, or visibility of
existing declarations changed, and no existing module besides the assigned item was adapted.

All three delivered Lean modules compile cleanly through lcompile.py. The local delivery
probe checks the axioms of all declarations. The generic sheafification helper has no sorry;
the target depends on the single explicitly named section-level hole. The unit sk-thm-p1
route is unchanged, and this node realizes none of its fixed steps directly.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_stalk_bijective`
(node `lem-weil-pbc-symmetric-algebra-affine-comparison-stalks`). Its entire proof is Lean,
with no tactic-local sorry.

Added one hole:
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_affineSectionComparison`
(node `lem-weil-pbc-symmetric-algebra-affine-section-comparison`), whose proof is exactly
`:= by sorry` in its own module. This is the section-level portion of the argument; the
basis extension, passage to stalks and cancellation are fully proved above it. This delivery
is a decomposition: one original hole closed, one lower hole added, net zero.

Also proved `AlgebraicGeometry.ringSheafification_restricted_stalk_bijective`
(node `lem-weil-pbc-ring-sheafification-restricted-stalks`) and its private restriction helper
`restrict_stalk_map_isIso`, with no sorry. No other holes are left in the delivered modules.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`
and `Sheaf.RingTheory.SymmetricAlgebraBaseChange` from the original module. They remain
imports of the new section helper because its proof plan needs them. No existing module
is claimed to leave the target import closure, so the pruned module count is zero.

The original node's direct proof dependencies are now just the affine section comparison,
the affine comparison map, and the proved restricted sheafification helper. Its former
section-base-change, symmetric-base-change, tilde, affine-chart and sheafification dependencies
remain needed through those helpers; they are not claimed as globally pruned.

The old proof dependency `lem-weil-pbc-module-restriction-open-immersion-colimits` is not
used as a theorem in this proof: neighbourhood cofinality replaces that step. The module
`Mathlib.AlgebraicGeometry.Modules.Sheaf` remains necessary to define the comparison target
and its restriction. No source module for this node can be removed from the import closure.

The complete old direct dependencies no longer directly used by the parent proof are:
`lem-weil-pbc-affine-open-spec-points`,
`lem-weil-pbc-quasi-coherent-affine-section-base-change`,
`lem-weil-pbc-symmetric-algebra-base-change`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-symmetric-algebra-sheaf-construction`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`lem-weil-pbc-ring-sheafification-space-underlying-abelian`, and
`lem-weil-pbc-stalk-sheafification-space`. Except for the module-restriction theorem,
these remain dependencies of the two helpers or of the comparison's definitions.

## Where the brief, the DAG or earlier work was wrong

The plan's cited base-change declarations do not directly assert the natural sectionwise
comparison that the stalk proof needs: tensor identifications, chart scalar transport and
naturality must be assembled. That precise section-level conclusion is the new item rather
than a renamed stalk theorem. The formal stalk argument can use bijection cancellation
instead of separately implementing its zero-kernel formulation.

The remaining section theorem was checked on empty affine opens, the zero module, empty
schemes (no stalk points), arbitrary modules with no finite-generation hypothesis, and
nonseparated schemes. It never assumes intersections of affine opens are affine; all
naturality is for inclusions of opens that individually are affine. For arbitrary affine V,
the tilde section identification uses quasi-coherent affine section base change on V≤top,
not an unsupported claim that every affine open is principal.

The local literature/stacks-project source files are absent on this machine. WANTED:
`literature/stacks-project/schemes.tex` (01I8), `constructions.tex` (01LN), `algebra.tex`
(0C6F), and `sheaves.tex` (007Z, 0087), for the two new nodes. The corresponding official
Stacks tag pages were read online. The proof sketches and origin records are marked as
agent assembly from those sources, not as quoted proofs. The original citation to 01CH
concerns symmetric-algebra stalks; the generic sheafification lemma uses 007Z and 0087.

LeanSearch returned HTTP Internal Server Error. Logged LeanFinder/Loogle searches and source
searches found constituent APIs but no specialized affine symmetric-algebra comparison.

## New nodes

`lem-weil-pbc-symmetric-algebra-affine-section-comparison`:
`lean/Sheaf/AlgebraicGeometry/SymmetricAlgebraAffineSectionComparison.lean`, theorem
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_affineSectionComparison`. One lower hole for
the affine-basis natural transformation, bijective components and section unit factorization.
Its node and docstring describe the two tensor identifications and their pure-tensor formulas.

`lem-weil-pbc-ring-sheafification-restricted-stalks`:
`lean/Sheaf/AlgebraicGeometry/RingSheafificationRestrictedStalks.lean`, theorem
`AlgebraicGeometry.ringSheafification_restricted_stalk_bijective`. Fully proved generic helper;
no quasi-coherence, no new axiom and no chosen unproved data. Its new node records the
sheafification-composition factorization and the final-neighbourhood colimit square.

No change records are needed: no existing statement, definition or public import changed.
The second reader narrowed a proof-only public import in the new generic helper and removed
its redundant LeftExact import; the two new modules did not previously exist.


## Second reading by J1

1. **Unchanged interfaces — pass.** Read all three modules and diffed the assigned module
   against the repository. The only existing declaration is
   `AlgebraicGeometry.SymmetricAlgebraSheaf.affineComparison_stalk_bijective`; its full
   signature, universes, hypotheses, conclusion and visibility are byte-for-byte unchanged.
   Only its proof and two plain proof imports changed. The other two modules are new.
   No definition was edited and there are no forced adaptations or change records.

2. **Proof and axioms — pass as a decomposition.** All three files compiled cleanly with
   `lcompile.py --all`. Explicit `#print axioms` in scratch copies reported only `propext`,
   `Classical.choice`, `Quot.sound` for `ringSheafification_restricted_stalk_bijective`.
   The target and `exists_affineSectionComparison` additionally report `sorryAx`, as expected
   from the one named section theorem. Read the finality square on colimit legs, basis
   extension into the tilde sheaf, basis hom-ext into the restricted algebra sheaf, germ
   lifting, and cancellation of bijections. They prove exactly the displayed statements.
   There is precisely one textual sorry, the complete body of the reported public theorem;
   no definition, axiom, unsafe declaration, opaque declaration, extern or implementation
   override was added. The existential transformation is used locally within a theorem,
   not selected as data for a definition from an unproved existence assertion.

3. **Split theorem — pass.** Read Stacks 01I8 (tensor/symmetric constructions on affines),
   01LN (canonical affine section base change in its proof), 0C6F (localization of symmetric
   algebras), 007Z (stalks of sheafification), and 0087 (algebraic sheafification), at their
   official tag pages. Read the imported `quasiCoherent_affine_section_baseChange`,
   `SymmetricAlgebra.baseChange_bijective`, and `affineComparison_toOpen` statements.
   These give the tensor identifications and the generator equality the new docstring
   uses; its restriction compatibility follows from the explicit pure-tensor formulas.
   This is genuinely a section calculation: it neither assumes nor restates the parent's
   stalk conclusion, and the passage from it to stalks is proved in the original module.
   For F=0 the calculation is ring base change; for an empty affine open the section rings
   and modules are zero. No point exists on an empty chart. Infinite modules cause no
   issue for symmetric algebra base change. For nonseparated X, only inclusions between
   individually affine opens are used, never affine intersections. LeanFinder search for
   “symmetric algebra of a quasicoherent module sections on affine opens compatible with
   restriction”, Loogle `SymmetricAlgebra, TensorProduct`, and rg in Mathlib's geometry,
   upstream geometry and lean/Sheaf found no duplicate of this section conclusion.
   Closing it requires assembling scalar transport and tensor naturality, rather than a
   short application of an existing theorem, so the named hole is retained.

4. **Route and pruning — pass after clarification.** The stalk proof already uses Mathlib's
   `restrictHomEquivHom`, `hom_ext`, `stalkFunctor_map_injective_of_isBasis` and germ APIs;
   no shorter specialized symmetric-algebra result was found. The unit sk-thm-p1 `realized`
   statement and all four step lists were read: this item is not one of those realizations,
   and no unit step is bypassed. No whole module is pruned. In the new generic helper,
   changed the proof-only public import of `Mathlib.Topology.Sheaves.Sheafify` to a plain
   import and exposed only `Mathlib.Topology.Sheaves.Stalks` for the signature. Removed
   redundant `Mathlib.CategoryTheory.Sites.LeftExact`; the helper still compiles.

5. **DAG agreement — pass.** JSON comparison shows only `proof`, `proof_deps`,
   `proof_origin` changed on the existing node. Its three steps match basis extension,
   stalk bijectivity of gamma, and restricted-unit cancellation in Lean. The two new nodes
   have source, statement dependencies, proof steps, origin, searches, blueprint ancestry,
   creation record, unit/chapter and verbatim Lean signatures. The generic helper cites
   the existing Mathlib-backed forgetting/sheafification nodes; its neighbourhood step
   is the proved adjunction/finality calculation. The section node cites the existing
   base-change and chart declarations, with no cycle back to the stalk theorem.

Changes from this reading: narrowed the new helper's proof-only import, removed its
redundant import, and made the direct-dependency pruning list explicit below. No proof
or mathematical statement needed repair. This remains one hole closed, one hole added,
net zero, plus the fully proved generic restricted-stalk helper.

