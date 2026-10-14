## What changed

Generalized the existing canonical CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq in the assigned module from one shared Ext universe to three independent universes. Its proof is unchanged and compiles. All nine existing code callers compiled unchanged against the generalized module, without warnings; each stayed within the 60-second limit. A fresh axiom probe for the theorem and private helper reports only propext, Classical.choice and Quot.sound. The temporary caller copies were removed after validation and are not part of the delivery. Updated the node Lean record and proof origin. Change record: coord/changes/ext-composition-independent-universes.md. The duplicate alias is already absent and all nine current code callers already use the canonical declaration; none needs editing.

## Proved and sorry left

CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq remains completely proved at the more general universes; the private singleComparison_hom is proved. Zero initial sorries, zero holes closed, zero holes added, zero split off. This is a signature generalization of a listed repair, not net hole progress.

## No longer needed

None newly pruned. No extra imports, duplicate alias, or new module. Both existing imports are needed. The duplicate exactFunctorCompositionComparison and its caller references were removed by earlier landings, not this session.

## Where the brief, the DAG or earlier work was wrong

The previous session treated the assignment as a proof task and refused an unchanged delivery. The final dispatch explicitly makes this a listed upstream repair. The cited upstream theorem is absent from both pinned Mathlib and the source-library Ext.Map module. Earlier changes ext-composition-canonical-name.md and ext-composition-remove-compatibility-alias.md already renamed the theorem and removed its compatibility alias. Relocating it into an unheld source module would add a public declaration without a forced compilation failure, contrary to the forced-adaptation rule. The remaining generalization here removes the independent-universe restriction of the canonical theorem without adding a duplicate or editing targets. Literal relocation into the cited source module is not performed.

## Second reading by R2

1. Compared the only delivered module byte for byte with the repository. The sole signature change is the declared generalization from one Ext universe to three independent Ext universes, recorded in coord/changes/ext-composition-independent-universes.md. All other signatures, both proof bodies, visibility and imports are unchanged. No target or definition changes. The nine code callers identified by downstream.py --uses match the change record; I compiled fresh unchanged copies against the sandbox module, all without warnings in 3.9–44.3 seconds. The temporary copies and their compiled artifacts were removed. Verdict: pass.

2. Read the whole proof, including the degreewise single-complex equalities, cancellation of comparison isomorphisms, and shifted naturality. The module compiles without warnings in 4.8 seconds. A scratch copy with #print axioms for mapExactFunctor_comp_mk₀_eq and singleComparison_hom compiles and reports only propext, Classical.choice and Quot.sound for each. No sorry, axiom, unsafe, opaque, implemented_by, extern, hollow definition or arbitrary existential witness occurs. Verdict: pass.

3. There are no split-off statements or new declarations. The generalized statement retains the same naturality equation; degree zero reduces to naturality of e, a zero class gives zero on both sides, and identity functors with the identity comparison give the reflexive equality. The unchanged proof checks with independent universes. Repeated searches using Loogle ("mapExactFunctor", "comp"), Lean Finder (successive exact functors and their composite), and rg over pinned Mathlib and both library roots. Online Loogle finds comp_mapExactFunctor and mapExactFunctor_comp_mk₀_natTransApp in newer Mathlib, but neither is present in pinned Ext.Map or the source extension. Pinned mapExactFunctor_comp preserves composition of Ext classes and does not compare successive functors. No available duplicate or shorter direct theorem was found. Verdict: pass.

4. Both imports are necessary: public Mathlib Ext.Map supplies the statement API; the plain proof import supplies the derived comparison maps, factorization equations and shift-compatible instances. The proof uses each of the three old proof_deps, so none is pruned and No longer needed is complete. Read sk-thm-p1's realized statement and all four steps: this generic comparison tool changes no unit step and bypasses none. Verdict: pass.

5. Compared the node with the repository and the Lean proof. Only its lean record and proof_origin change; the recorded Lean signature is exactly the delivered signature. Its existing proof steps accurately describe the single-complex comparison followed by shifted naturality, and proof_deps are unchanged and justified. There are no new nodes requiring new-node metadata. The informal node statement already allows independent categories and imposes no shared Ext universe. Verdict: pass.

Second reading changed only this report by adding the independent review and fresh validation results; no proof or metadata repair was needed. Holes closed: none. Holes added: none. This delivery is a listed interface repair, not net hole progress.
