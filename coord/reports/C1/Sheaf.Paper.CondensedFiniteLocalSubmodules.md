## What changed

Replaced the item theorem's hole by an explicit construction from a finite-family
comparison Hom factorization statement. The construction chooses the supplied local isomorphisms,
constructs the finite scalar extensions and their canonical adjoints, proves the adjoints
monic using a coefficient-linear projection splitting the extension unit, and computes
that their scalar adjuncts are isomorphisms. A finite family containing both directions
of every overlap supplies comparison maps. Cancellation against the pulled monomorphisms
proves that these maps are inverses; the forward equations are the required compatibility.
The existing theorem signature is unchanged.

Added CondensedLocalCoefficientAdjoints, an explicit construction API for local scalar
adjoints. Added CondensedFpHomStage, proving internal
finitely presented Hom factorization from qcqs section continuity by generators and
relations. Added CondensedCoefficientHomStage, proving finite coefficient Hom factorization
by evaluating the existing coefficient-complex colimit at degree zero. Added
CondensedCoefficientFamilyHomStage, proving simultaneous Hom factorization by extending
the individually descended maps to one upper field and using mixedScalarMap composition.
Added CondensedFiniteFamilyHomDescent for the remaining pullback/adjunction transport step.
All new imports used only by proofs are ordinary imports.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_compatible_local_monomorphisms`.
Added one hole in
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_family_hom_factorizations`, node
`lem-weil-pbc-condensed-finite-family-hom-descent`.
This is a decomposition, with one hole closed and one added, net zero; it is not an
axiom-free proof of the original theorem.

The new API theorems `isIso_finiteCoefficientLocalTensorMap`,
`mono_finiteCoefficientLocalAdjoint`, `finiteCoefficientLocalAdjoint_scalarAdjoint`,
`condensed_fp_hom_stage`, `condensed_coefficient_hom_stage`, and
`condensed_coefficient_family_hom_stage` are proved, with zero
local holes. Every new definition has an explicit body and contains no hole.

Verification: all six modules compile cleanly through lcompile.py. The axiom checks for
monicity, the scalar-adjoint equation, and all three Hom stage theorems show only
`propext`, `Classical.choice`, and `Quot.sound`. The item theorem still has `sorryAx`
from the one named transport lemma, as expected for this decomposition.

The remaining family theorem asserts forward and reverse homomorphisms, with compatibility
equations, for a finite family of schemes whose pairwise pullbacks are qcqs. It assumes no
cover, affine or pro-etale conditions and no quasi-separatedness of the ambient X. It makes
no assertion of monicity, scalar-adjoint invertibility, or inverse identities. It is strictly
a part of the original argument: the main module proves all those further assertions.
What still needs Lean is the coefficient/module transport along the inverse-image comparison
isomorphisms and the identification of the resulting equations with the canonical adjoints
using scalar-transitivity and unit naturality. The canonical finite-family Hom theorem already
proves the common-field step. The complete mathematical argument is in the remaining
hole's docstring and DAG node.

## No longer needed

No original public import is removed, because all three support the unchanged signature.
The item removes the ordinary proof imports
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus`, and
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, replacing them with
the family-Hom-descent module. Section calculus remains an indirect import.
The original target proof route through the internal-abelian-sheaf/module equivalence is
unused: the new Hom theorem works directly with internal modules. No explicit weakly-etale
localization argument is needed for overlap qcqsness; the standard scheme pullback instances
suffice. No eventual-equality enlargement is needed to enforce the overlap inverse identities:
monomorphism cancellation proves them at the chosen common stage. Eventual equality is still
used inside the proved finitely presented Hom stage theorem to descend relations.

The target node drops these six old direct proof dependencies:
`def-weil-finite-subextension-directed-set`,
`def-weil-pbc-condensed-e-module-category`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-proetale-qcqs-fp-section-calculus`,
`lem-weil-proetale-weakly-etale-localization`, and
`lem-weil-pbc-condensed-flat-coefficient-calculus`.
The finite-field and internal-module definitions remain statement dependencies;
the section-calculus and coefficient-field arguments remain indirect proof inputs. The projection API is imported from
SplitCoefficientDerivedFaithful, whose existing node still depends on flat calculus;
therefore this delivery does not claim to prune that entire transitive module closure.
The target's direct qcqs section-calculus dependency now goes through the named Hom APIs.
No claim is made that these modules are unused by other targets.

The second reader removed the unused proof import
`Mathlib.CategoryTheory.Filtered.Final` from CondensedCoefficientFamilyHomStage.
The retained hole's node also drops the inapplicable citations
`lem-weil-pbc-bounded-constructible-exact-scalar-extension` and
`lem-weil-pbc-module-constructible-pullback`: preservation of the global presentation
is explained directly, rather than inferred from their constructibility conclusions.

## Where the brief, the DAG or earlier work was wrong

The original plan's extra enlargement to enforce inverse equations is unnecessary once the
adjoints are known monic. The existing split-unit projection proof proves their monicity
without constructing a new faithful-flatness argument. The relevant finite presentation is
the library's global finite free cokernel presentation, so section continuity plus descent
of finitely many relations suffices directly in the internal-module category.

A transparent abbreviation of the extended model made dependent type matching expand the
scalar-extension construction repeatedly. The new construction uses a named definition and named adjunction equations.
The Hom interface is indexed directly by pairwise pullbacks, avoiding repeated conversions through
an unnecessary local-model record. No existing declaration or target
statement has been changed, and no other group's module has been adapted.

Edge cases checked in the arguments: the finite family and cover may be empty (choose E);
finite free generator or relation sets may be empty (filteredness supplies an upper object);
P and Q may be zero; the canonical Hom theorem permits arbitrary homomorphisms; only
qcqsness of each pairwise pullback, rather than Noetherian hypotheses, is used in the Hom stage argument.

## New nodes

`def-weil-pbc-condensed-local-coefficient-adjoints`: explicit finite local model, tensor map,
canonical scalar adjoint and split-unit monicity API.

`lem-weil-pbc-condensed-fp-hom-stage`: proved filtered-stage factorization of maps from a
finitely presented internal module on a qcqs scheme.

`lem-weil-pbc-condensed-coefficient-hom-stage`: proved factorization into a finite scalar
extension, using the coefficient-complex colimit and the preceding Hom theorem.

`lem-weil-pbc-condensed-coefficient-family-hom-stage`: proved simultaneous coefficient Hom
factorization, including the common upper-field construction and composition equation.

`lem-weil-pbc-condensed-finite-family-hom-descent`: the only new hole, comparison
homomorphisms in both directions on pairwise pullbacks, with their canonical-adjoint equations.

The existing finite-local-submodules node's proof, proof dependencies and proof origin are
updated to match the construction. No change record is required: existing interfaces and
definitions are unchanged.

## Second reading by C1

1. Compared every delivered module with the shared repository. Only
   CondensedFiniteLocalSubmodules already exists there; its complete theorem signature
   is byte-for-byte unchanged. Its three public imports and visibility are unchanged.
   The other five modules are new, with explicit definitions and no changed existing
   interface. No change record or forced adaptation is needed.
2. Read the construction and all proofs, then compiled the six modules with
   lcompile.py. The only delivered sorry is the named
   `exists_finiteCoefficient_family_hom_factorizations`; none occurs in a definition.
   No forbidden declaration or kernel-check bypass is present. A separate scratch
   import checks every public declaration's axioms; the constructed data and the
   proved scalar-adjoint and Hom-stage APIs use only propext, Classical.choice and
   Quot.sound. The main theorem and the explicitly retained transport theorem also
   use sorryAx, exactly as reported. Choosing the supplied isomorphisms uses actual
   Nonempty hypotheses, and the colimit witness determines its structure uniquely;
   no definition chooses arbitrary data from a holed existence theorem.
3. Read the upstream TwoColimit (Obj)/(Hom) paragraphs in the available
   weil-newtargets-master checkout, the qcqs section calculus, the coefficient
   diagram/colimit API and the finite-presentation definition. The retained hole
   has arbitrary local maps, a finite index, qcqs pairwise pullbacks, globally finite
   presentations and the specified isomorphisms; its conclusion asks only for the
   compatible maps. Monicity, tensor-adjoint invertibility and inverse identities
   are proved outside it, so this is a strict decomposition, not a renamed target.
   Checked the empty family (F=E), zero generators/relations (filtered nonemptiness),
   zero modules, and diagonal pairs. No ambient qcqs, cover or affine assumption
   enters its Hom descent. The docstring now specifies the transpose of each
   composite, the mixedScalarMap factorization and cancellation of u_j inverse/hom.
   New independent leanfinder, loogle and grep searches are in searches.jsonl;
   searched internal-module and condensed-coefficient library files as well.
   Mathlib's IsFinitelyPresentable.exists_hom_of_isColimit requires a categorical
   finite-presentability instance, whereas the input here is a finite-free cokernel
   presentation; no such bridge for these internal modules was found. The supplied
   generator/relation proof establishes the needed factorization directly.
4. The top-level reduction explicitly constructs q at every stage, proves monicity
   by the pulled split unit, and checks its scalar adjunct before using overlap Hom
   descent. Cancellation against the pulled monomorphisms proves both inverse
   identities. Reviewed the finite-generator lifts and eventual equality proof:
   the relation map is made zero at a common later stage, then the cokernel gives
   the factorization. The coefficient theorem evaluates the actual colimit in degree
   zero; the family theorem takes one upper field including E, also for no indices.
   No shorter existing applicable result was found. Removed one unused ordinary
   import. Tested removing the public Basic import; it is required for the monoidal
   structure in the statement, so it stays public. All six removed old proof_deps
   are now explicitly listed above. The unit sk-thm-properbasechange realized fields
   concern projective-line reduction and torsion assembly; none is bypassed or changed
   by this lower-level coefficient argument. No whole-module pruning is claimed.
5. Compared each node's statement, proof steps, proof_deps and Lean record with its
   module. The target node records the actual split-unit/Hom/cancellation route.
   The new nodes carry source, searches, provenance, chapter/unit and Lean records.
   Corrected the retained hole's proof citations: its global-presentation transport
   follows by mapping finite free cokernels and ring isomorphisms, not by applying
   the cited bounded-constructibility or constructible-pullback conclusions. Its
   dependencies now cite the coefficient-module comparison convention, the proved
   family Hom theorem and the canonical adjoint construction.

Second-reading changes: expanded the remaining hole's natural-language proof with
its adjunction calculation; corrected that node's proof/proof_deps/proof_origin;
removed the unused Filtered.Final import; completed the direct-dependency pruning
list. No theorem signature or definition body was changed. One original hole is
closed and one strictly smaller hole remains added: net zero, a decomposition.
