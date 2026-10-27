## What changed

Reduced the remaining coef_integral_finite_extension proof to three strictly partial
statements: comparison_invertibility (triangulation and invertible u,v), reductionPairing
(the signed double-dual and finite v,beta squares), and comparison_cocycles (identity,
composition and associator pentagon). Each has its own module, source, complete proof in
words and DAG node. The assembly proves constructibility preservation from the existing
sfIntegralScalarExtension_constructible, beta invertibility from u and v, the v evaluation
formula by adjunction transposition and completion transport, the beta evaluation formula
by counit naturality, and u reduction from its defining unique-map specification.

Moved the unchanged canonical maps, predicates and already proved u_existsUnique into
CoefIntegralFiniteExtensionCore to avoid a cycle; the item publicly re-exports it. Existing
public names, signatures and construction bodies are unchanged. Added the proved
u_reduction equation. Only the new proof dependencies are imported privately.

Change record: coord/changes/T8-integral-finite-extension-core.md. No source-library edit.

Validation: lcompile --all compiled Core and all three new statement modules. After
correcting categorical transport details, the final item compiled cleanly with no
warnings in 19.3 seconds. The original theorem signature and the relocated original
namespace were checked byte-for-byte unchanged. All JSON files parse; proof-dependency
sets equal the union of step uses, references exist, and the revised DAG is acyclic.

## Proved and sorry left

One original hole closed by decomposition:
WeilConjectures.coef_integral_finite_extension (lem-coef-integral-finite-extension).
Its proof is complete from named partial statements; it is not a sorry-free result.
The existing u_existsUnique proof is retained and the added u_reduction theorem is proved.
The private evaluation_transport and v_evaluation helpers are proved.

Three holes added, each strictly a part of the argument:
- WeilConjectures.IntegralFiniteExtension.comparison_invertibility
  (lem-sf-integral-finite-extension-invertibility).
- WeilConjectures.IntegralFiniteExtension.reductionPairing
  (lem-sf-integral-finite-extension-reduction-pairing).
- WeilConjectures.IntegralFiniteExtension.comparison_cocycles
  (lem-sf-integral-finite-extension-cocycles).

The item and Core have zero sorry bodies; the delivered set has three. This is a
one-to-three decomposition, not three newly completed mathematical proofs. Net holes
closed minus holes added is -2 before closure accounting by the project ledger.

## No longer needed

No mathematical dependency or module is claimed pruned. The existing proof imports
IntegralConstructibleReductionHom and CoefIntegralFiniteDualizingCoherence move with
u_existsUnique into Core, and remain needed there. Models remains publicly re-exported.
IntegralScalarExtensionConstructibleIntrinsic is still needed both in Core and the item.

The previous nine-step blueprint argument is distributed among the three lower lemmas;
its finite-free, finite dualizing, residue-Tor, normalized reconstruction, evaluation,
semilinear and tensor-associator tools remain needed through those lemmas and Models.
The item node now records its direct assembly dependencies. This is not a claim that
those lower proof-plan dependencies can be withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module has one remaining textual sorry, not the five mentioned in its historical
stage-2 review. Earlier work already proved u_existsUnique and moved the base models.
No current statement is weakened, disputed or replaced. The current blueprint proof
is followed; the unit route is retained.

## New nodes

- def-sf-integral-finite-extension-core: owns the relocated canonical maps/predicates
  and proved u reduction equation; no new hole.
- lem-sf-integral-finite-extension-invertibility: exactness and finite-free tests of u,v.
- lem-sf-integral-finite-extension-reduction-pairing: actual signed double-dual and two
  finite Hom comparison squares on normalized representative models.
- lem-sf-integral-finite-extension-cocycles: coefficient unit, composition and pentagon.

All inherit the original chapter and unit and cite the exact current blueprint passages.

## Statement corrected

(Reviewer, 2026-10-26.) The universally quantified presentation c of the composition
conjunct of coef_integral_finite_extension now carries first-variable evaluation
naturality. Without it c's adjunction is free at objects that are not K-flat complexes.
Composing it there with -1 negates v on one side of a composition clause, so the clause
was unprovable. comparison_cocycles assumes the same naturality for a, b and c.
reductionPairing assumes it also for the finite target presentations of mE and mL.
The assembly takes all of these from signedCalculus. The theorem has no users. Details
are in coord/changes/T8-integral-finite-extension-core.md.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
