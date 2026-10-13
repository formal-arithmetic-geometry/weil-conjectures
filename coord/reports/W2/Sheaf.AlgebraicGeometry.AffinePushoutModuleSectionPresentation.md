## What changed

Corrected affine_pushout_module_section_presentation by requiring delta to be the
canonical second inclusion t after the inverse-image ring unit, as its existing
proof text already required. Proved the affine comparison, first action and unit
normalization in a private helper from the existing affine-section comparison,
qcqs pushforward and scalar-restriction declarations. The complete parent proof
combines these with inverseImage_changeOfRings_unit_smul to prove the second action.
The sole caller, AffinePushoutFirstTensorSections, preserves its signature and now
retains the explicit canonical delta through the existing ring-presentation argument.
The second reading also proves the inverse-image unit scalar compatibility by the existing
semilinearity clause and tensor balancing. All three modules compile locally. Change record:
coord/changes/affine-pushout-module-canonical-delta.md.

## Proved and sorry left

Closed the corrected declaration
AlgebraicGeometry.Scheme.Modules.affine_pushout_module_section_presentation
(node lem-weil-pbc-affine-pushout-module-section-presentation). Its proof and its
private affine_pushout_module_section_presentation_equiv helper contain no sorry.
The caller affine_pushout_first_tensor_sections remains fully assembled with no sorry.

Also proved the newly introduced declaration
AlgebraicGeometry.Scheme.Modules.inverseImage_changeOfRings_unit_smul
(node lem-w2-inverse-image-change-of-rings-unit-smul), in its own new module.
The second reading closed its provisional sorry using
exists_inverseImageModuleInstances, linearity of the sheafification unit,
ModuleCat.ExtendScalars.smul_tmul, and tensor balancing.
No holes are added, and no sorry remains in the delivered modules. This closes the
one corrected parent obligation without replacing it by a lower hole. It does not
prove the false old arbitrary-delta statement, and the declarations still depend on
open theorems in the existing library, so this is not a claim of target closure.

## No longer needed

The abandoned sandbox modules AffinePushoutModuleSectionPresentationEquiv and
AffinePushoutModuleSectionPresentationActions are not delivered. The equivalence is
proved privately; the arbitrary-equivalence action statements were false and removed.
The earlier attempted equivalence node is removed from the sandbox and not delivered.

In the forced caller adaptation, the proof-only import
Sheaf.AlgebraicGeometry.AffinePushoutRingSectionPresentation is replaced by
Sheaf.AlgebraicGeometry.AffinePushoutRingAffineSections and
Mathlib.Algebra.Category.Ring.Constructions. The former existence-only ring presentation
cannot retain the required canonical delta equation. Its node
lem-weil-pbc-affine-pushout-ring-section-presentation is no longer directly needed by
this caller; the same lower affine ring-section pushout remains used. This is its
only direct importing module, so AffinePushoutRingSectionPresentation is pruned.
The caller's old proof_deps lem-weil-pbc-module-pullback-affine-sections,
lem-weil-pbc-quasi-coherence-scalar-restriction and pqf-lem-pushforward-qcoh
are no longer direct dependencies of the caller, but remain used through the parent;
their modules are not pruned.
The unused public import Mathlib.Algebra.BigOperators.Group.List.Basic is removed
from the main module; its only name user explicitly imports that module itself.
The main module retains all four original planned dependencies; none is pruned by the affine proof.
No unit-level step or statement is bypassed.

## Where the brief, the DAG or earlier work was wrong

Repair B9 (reviewer X-1a676, head 1a676f933): the new unit-scalar node's
blueprint.from previously named the created affine-presentation node, rather than
an imported blueprint ancestor, and omitted blueprint.same_as. Replaced its
blueprint object exactly as requested: ancestor thm-weil-pbc-finite-etale-lifting,
the specified essential-surjectivity place, all twelve intervening nodes in via
(nearest first), and same_as = []. The provenance correction changes no Lean
statement, proof, import, or proof dependency.

The original theorem accepted arbitrary delta while the docstring described the
canonical second inclusion. The polynomial-ring counterexample is recorded in the
change record. The earlier worker correctly noticed a problem with delta, but its
claimed absence of a section-module scalar action was inaccurate: the original
signature compiles, and the A-module G already supplies the C-action on G(V).
The previous generic action lemmas were false because an arbitrary linear equivalence
has no compatibility with a ring homomorphism. They are not part of this delivery.
The repair adds the missing canonical-inclusion hypothesis rather than proving a false
universal assertion. The sole downstream theorem keeps exactly its previous statement.
The new declaration is a genuine unit-action step, not a renamed parent conclusion;
it is now fully proved.

## New nodes

Whole-blueprint search for B9, performed 2026-10-13: searched all 2,338 imported
nodes (blueprint_kind present) in all 16 chapters, including nodes outside the
targets' reach, using tools/blueprint_refs.py search. Quoted phrase queries
"inverse image", "scalar", "semilinear", "change of rings", and "tensor unit"
returned 137, 78, 8, 2, and 1 candidates respectively. Queries "inverse image unit",
"008X", "03EK", and "01SB" each returned zero. Also searched dag/nodes with rg
for inverse-image, change-of-rings, semilinearity, and scalar/unit wording, and
filtered title/statement/source matches to module or tensor contexts.
Read the relevant imported statements: def-pc-derived-pullback,
def-weil-pbc-proetale-operations, def-weil-pbc-ambient-ringed-exchange,
def-weil-pbc-inverse-image, def-weil-derived-pullback-tensor-hom,
lem-kun-pullback-constant, lem-kun-tensor-unit, and lem-kun-change-of-rings-tensor.
These define derived or constant-coefficient pullback, exchange, tensor-unit
isomorphisms, or a coefficient quotient tensor comparison; none states the
sectionwise equation for the additive inverse-image unit, the ring unit, extension
along an arbitrary ring-sheaf map t, and linear sheafification. The semilinear
matches concern Frobenius/Galois actions and Tate modules. No imported blueprint
node states this equation in another form, supporting blueprint.same_as = [].
The imported ancestor is thm-weil-pbc-finite-etale-lifting; the created affine
presentation and the other intervening created nodes belong in from.via only.

lem-w2-inverse-image-change-of-rings-unit-smul states scalar compatibility of the
additive inverse-image unit followed by extension of scalars and sheafification.
Its source is Stacks Tags 008X and 03EK, used in the Tag 01SB tensor calculation.
The statement is proved without affine, quasi-coherence, or ring-pushout hypotheses,
and was checked on zero rings, zero modules and the empty open: both sides are zero.
The module is Sheaf.AlgebraicGeometry.InverseImageChangeOfRingsUnitSmul. The parent
node records its corrected canonical delta statement and the route actually used.
The caller node records the forced explicit-delta construction. Change record:
coord/changes/affine-pushout-module-canonical-delta.md.

## Statement corrected

The parent node's generic delta condition was missing. The added equality is precisely
the canonical second inclusion in the original proof text and Stacks Tag 01SB.
No base DAG node directly listed the parent in stmt_deps or proof_deps (the original
caller node listed only the older four plan dependencies), so statement_change.citers
is empty. The only Lean name user is AffinePushoutFirstTensorSections; it is adapted
with unchanged signature. The caller node now explicitly lists the parent dependency.

## Forced adaptations

Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections is unclaimed. Compiling its
original source against the corrected parent failed at line 155:
Tactic rcases failed: the supplied expression has type
(delta = t_W.comp etaR_V) → ∃ p, ... and is not an inductive datatype.
The proof did not supply the newly required canonical delta equation.

The import of AffinePushoutRingSectionPresentation is replaced by the lower
AffinePushoutRingAffineSections and Mathlib ring tensor construction imports.
Original lines 154–155 (obtain an unspecified delta) are replaced by lines 154–192:
construct the canonical delta and carry out the existing ring-presentation proof for
that same map. At line 194 the parent call gains rfl. Every changed line either retains
the canonical delta equation, proves the two ring conclusions for that delta, or supplies
the new argument; existing signatures and visibility are identical. The adapted file
compiled successfully against the corrected dependencies. No other module is adapted.

## Earlier second reading (a previous round; superseded)

1. Signatures and visible changes: PASS with the declared correction. Compared both
existing delivered modules by diff against the repository. The parent's only signature
change is hdelta, recorded verbatim in
coord/changes/affine-pushout-module-canonical-delta.md; the caller's declaration,
visibility and docstring are byte-for-byte unchanged. No definition or target is changed.
The first-inclusion polynomial example confirms that the old arbitrary-delta statement
was false. The sole name user is the adapted caller. The public List.Basic import removal
is deliberate and recorded; the caller has its own explicit import.

2. Proof validity: PASS. All three files compile locally in import order without warnings.
There is no sorry in any delivered module, no forbidden declaration/attribute, and no
hollow definition. The private affine comparison is constructed by commuting tensor
factors and transporting the canonical comparison through kappa inverse; its first
action and normalization determine the comparison on all pure tensors. The caller
constructs delta explicitly rather than selecting an arbitrary witness. The section
comparison chosen from the existing theorem is determined on pure tensors, and the
linear equivalence is obtained from its bijectivity, so no arbitrary data is chosen
from an unproved mere existence assertion. Axiom-print scratch copies and the delivery
probe check the declarations against the permitted axiom set. Explicit #print axioms
shows only propext, Classical.choice and Quot.sound for the corrected parent and the
new unit lemma; the caller was previously reported to have sorryAx from its affine ring-section dependency;
the current compiled snapshot shows only the three permitted axioms for it as well.

3. New statement: PASS, now proved. Read the inverse-image construction and its actual
chosen module instances, and checked the new equation for identity maps, zero rings,
zero modules and the empty open. It is the canonical unit's semilinearity followed by
linear sheafification and tensor balancing, strictly smaller than the affine parent.
Repeated Mathlib searches with different wording (Lean Finder, Loogle and grep), plus
rg over Sheaf and WeilConjectures, found the balancing tools and existing semilinearity
clause, not an existing combined theorem. The second reading used those tools to close
its provisional sorry. Its node and complete sourced docstring remain. Source checks:
https://stacks.math.columbia.edu/tag/008X,
https://stacks.math.columbia.edu/tag/03EK and
https://stacks.math.columbia.edu/tag/01SB.

4. Route and pruning: PASS. The affine comparison already takes the existing canonical
section theorem, qcqs pushforward and scalar-restriction route; no shorter independent
comparison was found. The second action now takes the existing semilinearity clause
directly via the proved new lemma. Removed the unused List.Basic import from the parent;
all added proof imports are plain imports. The caller's changes are restricted to the
forced canonical-delta adaptation; its inherited plan imports are preserved. Checked
all old proof_deps: the parent's four remain; the caller's three no longer direct
ones are reported above and still used through the parent. The ring-presentation
module loses its only direct importer. Read dag/units/sk-thm-p1.json: none of the
changed/pruned nodes realizes a unit statement or step, and every realized route stays.

5. Nodes: PASS. Read all three sandbox nodes against their declarations and proofs.
The new node has all required creation, blueprint, source, statement, Lean and search
fields, and its recorded signature agrees with the module. Updated its proof and
proof_origin to the now formalized semilinearity/balancing route. Parent and caller
proof_deps agree with the written proofs. The parent's statement_change has the sole
intentional correction; checked the repository for direct DAG citers (none).

Changes by the second reader: proved inverseImage_changeOfRings_unit_smul, removed
the parent's unused public List.Basic import, updated the new node's proof description
and source document label, completed the pruning list, and revised the report and
change record to say that no lower hole remains. No existing declaration signature
was changed beyond the first worker's recorded canonical-delta correction.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections
Original against changed dependencies failed:
```
/tmp/forced-adaptation-zvrpqoon/lean/Sheaf/AlgebraicGeometry/AffinePushoutFirstTensorSections.lean:155:9: error: Tactic `rcases` failed: `x✝ : δ =
    (CommRingCat.Hom.hom (t.hom.app (op (f ⁻¹ᵁ V)))).comp
      (CommRingCat.Hom.hom
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f.base) CommRingCat (𝓙↥X)
                      (𝓙↥U)).unit.app
                ((TopCat.Sheaf.pushforward CommRingCat f.base).obj U.sheaf)).hom.app
          (op V))) →
  ∃ p,
    (∀ (c d : ↑Γ(U, f ⁻¹ᵁ V)) (n : ↑(G.val.obj (op V))),
        (CommRingCat.Hom.hom (b.hom.app (op (f ⁻¹ᵁ V)))) c • p (d ⊗ₜ[↑Γ(X, V)] n) = p ((c * d) ⊗ₜ[↑Γ(X, V)] n)) ∧
      (∀ (c d : ↑Γ(U, f ⁻¹ᵁ V)) (n : ↑(G.val.obj (op V))), δ c • p (d ⊗ₜ[↑Γ(X, V)] n) = p (d ⊗ₜ[↑Γ(X, V)] (c • n))) ∧
        ∀ (n : ↑(G.val.obj (op V))),
          p (1 ⊗ₜ[↑Γ(X, V)] n) =
            (ConcreteCategory.hom ((κ.inv.app G).val.app ((Opens.map f.base).op.obj (op V))))
              ((ConcreteCategory.hom
                  (((Classical.choose ⋯).unit.app
                          ((SheafOfModules.restrictScalars
                                ((sheafCompose (𝓙↥X) (forget₂ CommRingCat RingCat)).map
                                  (have this := { hom := f.c };
                                  this))).obj
                            G)).val.app
                    (op V)))
                n)` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-zvrpqoon/.lbuild) [23.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by W2

1. Visible changes: PASS. Repeated the full diffs of both existing modules against
   the repository. The only existing signature change is the recorded canonical hdelta
   condition; the caller signature and both existing docstrings are unchanged. The
   polynomial example in the change record explains why arbitrary delta was false.
   No definition or target statement changes. The only name user is the adapted caller.

2. Proof validity: PASS. Compiled all three delivered files in import order without
   errors or warnings (8.7, 27.1, and 24.1 seconds). Scratch-copy #print axioms checks
   for the parent, the new unit theorem and the caller each show exactly propext,
   Classical.choice and Quot.sound, with no sorryAx in this compiled snapshot.
   There is no sorry or forbidden declaration in any delivered module. The section
   map is fixed on pure tensors, and LinearEquiv.ofBijective supplies its inverse;
   the canonical delta is explicitly constructed, rather than chosen arbitrarily.

3. New statement: PASS. The scalar-unit equation is fully proved, not a remaining
   split-off hole or a renamed parent. Read exists_inverseImageModuleInstances and
   inverseImageModuleInstances: the proof uses the semilinearity clause for exactly
   the instance chosen by the construction. Linearity of sh and the two tensor
   balancing identities complete the equation. For identity maps it is ordinary
   tensor balancing; zero rings, zero modules and the empty open give zero on both
   sides. Fresh Lean Finder, Loogle and grep searches using scalar-action and
   sheafified-extension wording found Sheafify.map_smul and ExtendScalars.smul_tmul,
   but no existing combined equation. Read Stacks Tags
   [008X](https://stacks.math.columbia.edu/tag/008X),
   [03EK](https://stacks.math.columbia.edu/tag/03EK), and
   [01SB](https://stacks.math.columbia.edu/tag/01SB) against the stated construction.

4. Route and pruning: PASS. The private affine comparison uses the existing canonical
   section comparison, qcqs pushforward and scalar restriction. The second action
   is a direct unit calculation followed by commuting the B-section scalars. All
   old parent proof dependencies remain; all caller dependencies no longer directly
   used are listed under No longer needed. RingSectionPresentation has only this
   caller as an importer, so the replacement removes it from this route. The unused
   public List.Basic import is deliberately removed only from the parent; the caller
   imports it explicitly for its List-valued conclusion. The caller's inherited
   imports are left within the forced-adaptation boundary. Read sk-thm-p1.realized:
   no changed or pruned node realizes its statement or a step, so that route remains.

5. Nodes: PASS. Compared all three node statements and Lean records with the actual
   declarations and their proof steps. The union of each proof's uses equals its
   proof_deps. The parent statement_change records its sole correction and has no
   base DAG citers; the caller now records its actual parent dependency. Verified
   the new node's B9 repair against the return verbatim: from.node is the imported
   thm-weil-pbc-finite-etale-lifting, via contains all twelve intervening created
   nodes in the requested order, and same_as is []. Its source, creation, searches,
   Lean record, proof and proof_origin describe the fully proved smaller unit step.
   The whole-blueprint search and the inspected competing statements are documented
   in New nodes.

Changes in this reading: appended this independent review and corrected the report's
outdated caller-axiom observation for the current compiled snapshot. The existing Lean
proofs and the repaired B9 provenance needed no further changes. No holes were added.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffinePushoutFirstTensorSections
Original against changed dependencies failed:
```
/tmp/forced-adaptation-gvn3aqjg/lean/Sheaf/AlgebraicGeometry/AffinePushoutFirstTensorSections.lean:155:9: error: Tactic `rcases` failed: `x✝ : δ =
    (CommRingCat.Hom.hom (t.hom.app (op (f ⁻¹ᵁ V)))).comp
      (CommRingCat.Hom.hom
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f.base) CommRingCat (𝓙↥X)
                      (𝓙↥U)).unit.app
                ((TopCat.Sheaf.pushforward CommRingCat f.base).obj U.sheaf)).hom.app
          (op V))) →
  ∃ p,
    (∀ (c d : ↑Γ(U, f ⁻¹ᵁ V)) (n : ↑(G.val.obj (op V))),
        (CommRingCat.Hom.hom (b.hom.app (op (f ⁻¹ᵁ V)))) c • p (d ⊗ₜ[↑Γ(X, V)] n) = p ((c * d) ⊗ₜ[↑Γ(X, V)] n)) ∧
      (∀ (c d : ↑Γ(U, f ⁻¹ᵁ V)) (n : ↑(G.val.obj (op V))), δ c • p (d ⊗ₜ[↑Γ(X, V)] n) = p (d ⊗ₜ[↑Γ(X, V)] (c • n))) ∧
        ∀ (n : ↑(G.val.obj (op V))),
          p (1 ⊗ₜ[↑Γ(X, V)] n) =
            (ConcreteCategory.hom ((κ.inv.app G).val.app ((Opens.map f.base).op.obj (op V))))
              ((ConcreteCategory.hom
                  (((Classical.choose ⋯).unit.app
                          ((SheafOfModules.restrictScalars
                                ((sheafCompose (𝓙↥X) (forget₂ CommRingCat RingCat)).map
                                  (have this := { hom := f.c };
                                  this))).obj
                            G)).val.app
                    (op V)))
                n)` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-gvn3aqjg/.lbuild) [26.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
