## What changed

Repair of reviewer C-20c3f's return of delivery 20c3fdab889. Compared the
returned packet with current server sheaf-dag 9c9e42f34cebc56330dbbc79381dc4c73015c7fc.
The packet now changes only BrownHypotheses and its existing integral Ext criterion
node. No other existing module or node is delivered.

Retained the requested Tor route: the proved private theorem
CategoryTheory.brownHypotheses_integral_ctf_eq_bc derives integral Dctf=Dbc from
the existing scalar Tor bound, stratified descent, and bounded-cohomology Tor interval.
The lower cohomological bound min(a,b) handles zero objects with reversed initial
bounds. CategoryTheory.brownHypothesesFor_padicIntegers_iff_ext_bounded uses this
equality and congrArg localizingClosure. The integral criterion node records this route.

ExceptionalInverseImageExistence, sk-thm-existence, and IntegralConstructibleCompactness
are left byte-equal to current main by omitting their sandbox adaptations. In particular,
IntegralConstructibleCompactness retains its original public import. Removed the
unlanded LocalizingExceptionalCoefficientTransport module and its ambient-transport
node from the packet. Also dropped the optional ContinuousCoefficientLiftIso module
and node, restored the item's original local finiteCoefficientLiftIso proof verbatim,
and omitted the noetherian-criterion node adaptation. Removed the obsolete change record.
All public signatures, definitions, instances, attributes, and target statements stay as on main.

Validation: lcompile.py accepted BrownHypotheses in 35.8 seconds and the original,
byte-identical ExceptionalInverseImageExistence consumer against it in 46.0 seconds.
Both checks completed with exit code 0 and no diagnostics. The temporary unchanged
consumer copy was removed after this check. deliver3.py runs the remaining delivery
and independent-reader preflight checks before pushing.

## Proved and sorry left

Closed 0 of the original 1 holes. Added 0 holes. Split off 0 statements.
CategoryTheory.brownHypotheses_integral_ctf_eq_bc is proved and used by the existing
integral Ext criterion; this is a proof-route change, not a newly closed hole.

The sole remaining sorry is CategoryTheory.brownHypotheses,
node sk-lem-brown-hypotheses. Its original signature, named sorry, and existing
STATEMENT-DISPUTED notice remain. No other module with a sorry is added or changed.

## No longer needed

Removed the item's direct proof import Sheaf.Paper.LocalizingClosureCtfEqualsBc.
The integral criterion no longer uses det-def-localizing-closure-ctf-equals-bc or
AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc. Its replacement inputs are
lem-sfb-padic-constant-local-model-tor, lem-sfb-stratified-tor-interval-devissage, and
lem-sfb-cohomology-tor-interval, imported privately from their existing modules.

The broad comparison module remains transitively imported through the unchanged
IntegralConstructibleCompactness dependency. Project-source import traversal finds
no modules removed from or added to the item's import closure. No module is withdrawn,
no target-closure pruning is claimed, and no unit statement or route is bypassed.

Both unlanded helper modules and their nodes are absent from this repaired packet:
Sheaf.Paper.LocalizingExceptionalCoefficientTransport with
lem-sfb-ambient-exceptional-coefficient-transport, and
Sheaf.Topology.ContinuousCoefficientLiftIso with def-sfb-continuous-coefficient-lift-iso.
They are absent on main as well; these are packet removals, not library withdrawals.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly justified an ExceptionalInverseImageExistence
adaptation by a 65-second timing. The independent reviewer compiled the original
consumer against the delivered item in 37.1 seconds, essentially its 37.2 seconds on
main. That adaptation was unforced, as was the public-import drop in
IntegralConstructibleCompactness. Both are removed exactly as requested. The earlier
945-module item-closure pruning claim relied on that rejected import drop and is withdrawn.

The original arbitrary-field Brown assertion remains disputed as documented in its
existing source. This repair preserves that statement and its hole, and retains only
the valid integral comparison proof and the existing conditional Ext criterion.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "c6f9dde28ed75b49cfcada5e294cf92fabdb5a70"}, "results": {"Sheaf.Paper.ExceptionalInverseImageExistence": {"hash": "e047ddc64ca96bb191cbf95acc82e09bbcecd38a", "status": "OK"}, "Sheaf.Paper.LocalizingExceptionalAdjoint": {"hash": "9b80929ae886e8305a73db59aae3e626c6c33cd3", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso": {"hash": "80cf11f0cc781fe2530a33ebe045d127e0d1bae7", "status": "OK"}, "Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField": {"hash": "40b1ac159f94b5a3cd0b71c7acef53f076a729f5", "status": "OK"}}, "seconds": 113, "time": "2026-10-28T08:48:19+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
