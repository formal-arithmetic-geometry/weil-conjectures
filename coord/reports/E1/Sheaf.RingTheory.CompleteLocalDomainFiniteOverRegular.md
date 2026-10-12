## What changed

Completed the proof body of IsLocalRing.complete_local_domain_finite_over_regular without
changing its signature or existing docstring. Added private proof imports of the residue-
preserving parameter construction, the power-series structural theorem, complete-module
finiteness, Mathlib dimension inequalities, and adic-completeness transport.

Added Sheaf.RingTheory.CompleteLocalDomainResidueParameterMap. Its single theorem retains
surjectivity of A → R → R/m_R for the SAME map having the parameter properties. The existing
CompleteLocalDomainParameterMap does not retain this necessary property. The new statement
stops before finiteness or injectivity of A → R and before any image-subring conclusion.
The remaining argument genuinely proves those assertions: complete-module finiteness,
integral contraction of prime chains, contradiction from finite equal dimensions, transport
of regularity and completeness to the image, maximal-ideal contraction, and the explicit
bijective quotient map. Updated the parent DAG to this proof and supplied the new node.

Source read: Stacks 032D, label lemma-complete-local-Noetherian-domain-finite-over-regular,
both cases; the local copy at work-bp/sheaf/literature/stacks-project/algebra.tex and the
Stacks tag page. This keeps the source's coefficient/parameter, finiteness, dimension, and
image-subring route. This node is not itself a unit statement or a realized unit step.

## Proved and sorry left

Closed: IsLocalRing.complete_local_domain_finite_over_regular (one original hole).
The item's module now has no sorry.

Added and left: IsLocalRing.complete_local_domain_residue_parameter_map, node
lem-weil-pbc-complete-local-domain-residue-parameter-map (one named hole in one new module).
This is a decomposition: one upper hole closed and one strictly smaller construction hole
added, net zero delivery holes. It does not assert finiteness, injectivity, regular image
subring existence, or the parent residue equivalence. Imported existing theorem
Module.finite_and_span_eq_top_of_adicComplete remains unproved in its existing module;
its hole is not introduced by this delivery. The power-series structural theorem is proved.
Both delivered files compile cleanly using lcompile.py --all.

## No longer needed

No import from the original item's four public imports was removed: all serve its signature.
The provisional proof imports Mathlib.RingTheory.IntegralClosure.Algebra.Basic,
Mathlib.RingTheory.Ideal.GoingUp, and Mathlib.RingTheory.LocalRing.ResidueField.Basic
were removed after compilation established they are already available from retained imports.

The proof does not use Sheaf.RingTheory.IntegralExtensionDimension or its declaration
RingHom.integralExtensionDimension (node lem-weil-pbc-integral-extension-dimension).
Mathlib's strict contraction and maximal contraction lemmas supply its needed facts directly.
It also does not use CompleteLocalDomainFiniteOverRegularCore,
CompleteLocalDomainFiniteOverRegularResidue, or CompleteLocalDomainParameterMap and their
split nodes. The last assertion omits the residue property and is superseded on this route
by the residue-preserving construction. Whether these modules remain reachable from other
target branches is for the global queue to determine.

The coefficient-subring, parameter, change-ideal, dimension-drop, Artinian-quotient, and
power-series-evaluation steps remain needed within the new construction node; they are not
claimed pruned. The old onto-completion route of step 4 is replaced there by the already
stated complete power-series universal property.

## Where the brief, the DAG or earlier work was wrong

The original item has no proof-dependency imports, despite the generic brief describing them
as already present. Its eight-step outline is usable, but the existing parameter-map
interface loses residue surjectivity for the chosen map. An arbitrary finite regular subring
cannot supply the parent's residue isomorphism: R = ℂ with real subfield R₀ = ℝ is the
counterexample documented in the retirement change record. This delivery uses no retired
residue declaration and never infers residue surjectivity from finiteness alone.

The construction statement was checked on zero parameters (field case: a zero-dimensional
local domain is a field; Cohen case: a one-dimensional mixed-characteristic domain), and on
positive-characteristic fields. Constant series preserve the coefficient residue
surjectivity in all cases. No arbitrary witness is used in a definition: all existential
witnesses are eliminated inside the theorem proof, and the range equivalence is constructed
from the actual map only after its injectivity has been proved.

Searches: LeanFinder found Noether normalization and finite Jacobson maps but no parameter
construction; Loogle found the residue-map API; msearch grep and direct rg found the existing
parameter-map and Cohen power-series presentation modules. LeanSearch returned Internal
Server Error and is recorded unavailable, not as a successful negative search.

## New nodes

lem-weil-pbc-complete-local-domain-residue-parameter-map: Stacks 032D's coefficient and
parameter construction, with the residue-surjectivity property retained. Its proof outline
states both characteristic cases, evaluation, equal dimension, Hausdorffness, finite reduction,
and surjectivity from constants. Existing construction dependencies are reused in its DAG.
No existing definition, statement, public visibility, or dependent module was changed; no
change record or forced adaptation is required.

## Second reading by E1

1. Compared both delivered modules with the repository versions. The existing target
   declaration is byte-for-byte unchanged in its signature and docstring; the added
   module and node are the only new interfaces.
2. Compiled both modules with `lcompile.py --all`. The target proof has no `sorry`; the
   only remaining hole is the named split theorem
   `IsLocalRing.complete_local_domain_residue_parameter_map`. No forbidden declarations or
   hollow definitions occur.
3. Checked the split statement against the construction in Stacks 032D, including zero
   parameters and field cases. It is strictly weaker than the parent target: it supplies
   only the parameter map, dimension, Hausdorffness, finite reduction, and residue
   surjectivity, and does not assert finiteness, injectivity, or an image subring.
   Searches found no duplicate declaration in Mathlib or the library.
4. Followed the proof from the parameter construction through finite-module reduction,
   dimension and injectivity, and transport to the range. The route preserves the unit's
   parameter and power-series steps. The private imports retained are all used; the report
   records the removed provisional imports and unused old proof dependencies.
5. Checked the DAG proof and `proof_deps` against the Lean proof, including the new split
   node and its source/docstring. The unit record remains unchanged and the new node is
   marked `split` with the required metadata.

Changed only this report section after review; no Lean statements, definitions, or DAG
proof routes required repair.
