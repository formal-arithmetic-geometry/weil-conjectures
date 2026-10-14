## What changed

Proved `AlgebraicGeometry.Scheme.field_torsor_component_galois_group` in
`Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup` with its original
signature, universes, visibility, hypotheses, and conclusion.

Added two fully proved private helpers. `torsor_translation_unique` factors a map
from a nonempty single-point scheme through the torsor coproduct isomorphism and
proves that the translation element is unique. `component_embedding_factors`
uses this translation and the open immersion to factor any two embeddings of the
component field through a K-algebra endomorphism of that field.

Etaleness gives finite separability directly. The second helper shows that the
normal closure inside an algebraic closure is the range of one embedding, proving
normality. For the group conclusion, assign to each field automorphism the unique
translation corresponding to its inverse; this gives an injective monoid
homomorphism into G. `MonoidHom.ofInjective` identifies its domain with its image
subgroup. The inverse is necessary because Spec is contravariant.

Replaced the proof import of the Galois-set classification with proof imports of
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`Mathlib.RingTheory.Etale.Field`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Limits`. All three are used; testing
removal of the last import produced an unknown-identifier error for
`exists_comp_sigmaι_eq_of_subsingleton`, so it is retained. The two public imports
are unchanged. No definition or public interface was changed and no adaptation
or change record is needed.

Updated the existing node's `proof`, `proof_deps`, and `proof_origin` to describe
this direct proof. The declaration's existing docstring retains the original
valid alternative Galois-set argument; the node and proof comments document the
implemented shorter route. The unit's statement and steps are preserved.

Verification: the entire module compiles without errors or warnings using
`lcompile.py`. The required delivery dry run also compiles the axiom probe.
The original theorem and both private helpers contain no sorry.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.field_torsor_component_galois_group`
(node `lem-sbc-field-torsor-component-galois-group`).

Also fully proved the private helpers `torsor_translation_unique` and
`component_embedding_factors`. No holes were added, no statements were split off,
and no sorry remains in any delivered Lean declaration. This is a proof, not a
decomposition.

## No longer needed

Removed the direct proof import
`Sheaf.FieldTheory.EtaleFieldGaloisClassification`, and removed the dependency
`lem-exc-etale-field-galois-classification` from the item's `proof_deps`.
Its transitive helper `Sheaf.FieldTheory.OpenSubgroupFixedField`
(node `lem-exc-etale-open-subgroup-fixed-field`) is likewise unnecessary for this
proof. These modules may still be needed by other library clients.

The proof needs neither the geometric Galois-set classification nor its
open-subgroup fixed-field correspondence, topology, normal kernel, and quotient
construction. It also avoids the finite-product decomposition of the total
space. No existing unit statement or unit proof step is bypassed: the shorter
argument is entirely within this auxiliary component calculation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original DAG route is longer than
needed: directly factoring translations through j gives embedding factorization,
and Mathlib's normal-closure API proves normality without constructing a
continuous absolute-Galois action or its quotient. Unique translations of inverse
automorphisms give the group embedding directly.

The trivial-group and split-torsor cases require no separate hypothesis or case
split. Field spectra are nonempty and have one point; the proof never assumes
that the entire torsor is connected. All local choices are either the explicit
Mathlib algebraic-closure embedding construction or uniquely determined
translations from a theorem proved here. No arbitrary object is chosen from an
unproved existence theorem.


## Second reading by P2

1. **Interface unchanged: pass.** Read the complete diff of the only delivered
   Lean module against the repository. Compared the existing theorem signature
   byte for byte, including its universes and all hypotheses and conclusions:
   identical. Both public imports and public visibility are unchanged. The only
   additions are fully proved private helpers and proof-only imports. No target,
   definition, or other module is changed; no change record is required.
2. **Kernel proof: pass.** Independently compiled the delivered module with
   `lcompile.py`: no errors or warnings. A scratch copy with `#print axioms` for
   the public theorem and both private helpers reports exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each, without `sorryAx`. The delivered
   source contains no sorry, axiom, unsafe, opaque, implemented_by, extern, or
   kernel-check bypass. Read both helpers and the entire public proof. The
   translated embedding factors through the open immersion by the one-point
   image calculation; this proves inclusion of every embedding range in one
   fixed range. The inverse automorphism in the final translation map gives
   the correct multiplication order. All witnesses used in this proof come
   from proved statements, including Mathlib's algebraic-closure embedding.
3. **New statements and small cases: pass.** No statement was split off and no
   hole was added. The two private helpers are fully proved proper parts of the
   argument, not restatements of the item. Nonemptiness is explicitly needed
   for uniqueness of a coproduct summand; empty sources are excluded. Field
   spectra satisfy both one-point and nonempty assumptions. For G trivial and
   for split torsors the automorphism image is trivial, and disconnected total
   spaces require no extra assumption. Independently searched the library and
   Mathlib with rg and LeanFinder using the query "Two morphisms from a
   connected scheme to a finite group torsor over the same base differ by a
   unique group element". The abstract pre-Galois-category candidates require
   additional categorical structures and give no shorter scheme-torsor proof.
   No existing replacement for these helper interfaces was found.
4. **Route and pruning: pass.** The proof uses the proved upstream coproduct
   factorization and Mathlib's etale-field, normal-closure, and subgroup-image
   APIs directly. The three proof imports provide these APIs; public imports
   supply the signature. The only old proof dependency,
   `lem-exc-etale-field-galois-classification`, and its removed module are
   explicitly listed under No longer needed. Read
   `dag/units/sk-prop-input-spreading.json`: this auxiliary component node is
   absent from its realized statement and steps. The unit route and records
   are unchanged; this proof replaces only the auxiliary calculation below it.
5. **DAG agrees: pass.** Compared the complete existing node JSON: only `proof`,
   `proof_deps`, and `proof_origin` changed. Its five proof steps describe the
   Lean construction, its empty proof_deps correctly records that no other DAG
   proof node is invoked, and its Lean signature remains unchanged. There are
   no new nodes or unreported dependencies.

Second reading changed only this report, recording the independent review and
axiom checks. The Lean proof and node changes were correct and needed no repair.
Closed one original hole; added zero holes; split off zero statements.
