# Stage-1 report: sk-def-kernel

## Files written

- `dag/nodes/sec-fourier-transform/sk-def-kernel.json`: definition; split into the existing Artin–Schreier construction; Mathlib searches found no matching sheaf/kernel definition. No new nodes or Mathlib leaves.
- `dag/units/sk-def-kernel.json`: only `realized` and `realized_by` filled. The current definition is realized by sk-def-kernel and has no proof steps.
- `citations.json`: empty list, because the item is a definition and has no proof-step citations.

## Attachments

None. I read `lean/WeilConjectures/FourierTransform/Defs.lean:138-157`, including `AlgebraicGeometry.Etale.fourierKernel` at line 154, and its construction `artinSchreierSheafZMod` in `FourierTransform/ArtinSchreier.lean:492-516`. The definition has a one-line body without sorry, but assumes `[CharP Γ(W, ⊤) p]`. The current detailed blueprint explicitly requires only p=0 in Γ(W,O). For W empty its section ring is the zero ring, where p=0 but CharP(_,p) fails for prime p (already 1 casts to zero but p does not divide 1). Therefore this declaration does not cover every allowed input and is not an exact attachment. The affine-space and fourierIntegrand declarations do not remove that restriction.

## WANTED

None.

## Statement and import corrections

STATEMENT-DISPUTED: the imported statement uses F_p without explicitly quantifying a prime p and says only 'characteristic p'. I made primality explicit and used the intended condition p=0, verbatim in meaning from `main-20261015/blueprint/sec-fourier-transform/sk-def-kernel/def-fd-kernel.md`. This repairs the typing and resolves the zero-ring ambiguity without adding a nonemptiness hypothesis.

The current `_section.md` has no integrand clause despite its historical title. Its formula is a sheaf of modules for arbitrary commutative Lambda with p invertible, rather than a bounded constructible adic complex. I retained that coefficient category: the optional finite-field application cites the existing acyclic detailed convention node def-fourier-set for k0=F_q, without imposing its adic coefficient restrictions on the general definition. The stored `dag/units/sk-def-kernel.json` still reproduces the older master statement, which contains the integrand; I changed only its allowed realization fields and report the stale text for the maintainer. The current main-20261015 definition takes precedence, as the brief requires.

The sketch dependency chain sk-def-as -> sk-def-char -> sk-def-fourier-set -> sk-def-kernel is cyclic. The item needs the general construction of the Artin–Schreier sheaf for k=F_p, not the conventions about a fixed nontrivial adic character. I use the existing `def-fd-artin-schreier-sheaf` through its current blueprint_update, whose statement explicitly provides this general construction and defines L_(Psi,f)=f^*L_Psi. The synonymous sketch is still the source's route, but is not needed as a second dependency. The first server dry run required the unit's conventions unit to remain reached, so I retained that dependency through its acyclic detailed notion def-fourier-set, used explicitly to introduce k0 in the application paragraph. No other node was changed. The vector-bundle paragraph now introduces k0=F_q, S0, the dual and evaluation explicitly and uses the same Psi as the defining formula.

## Not duplicates

No new nodes. The blueprint search for 'Fourier kernel' found def-fd-kernel, whose current blueprint_update states the same definition; it is recorded in `blueprint.same_as`. I did not create a duplicate. Other hits (kernel lissity, convolution, transform, perverse transform) assert properties or define different constructions. Searches of the DAG for Artin–Schreier sheaves found the existing general detailed definition, reused here.

## Review by Q35

I read the entire current source of the item, `literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-kernel/_section.md`, its detailed `def-fd-kernel.md`, and the current sketch and detailed Artin–Schreier definitions. I also read Laumon's paper, PDF pages 10-12 (printed pp. 139-141): (1.1.3.6) defines L(f) by inverse image and (1.2.1) uses the evaluation pairing E x_S E' -> G_a. Laumon supports the vector-bundle notation, while the generalized ring-coefficient statement is taken from the current blueprint; I do not attribute that extra generality to Laumon. No SGA route is used.

I also opened def-fourier-set.json: it explicitly fixes q=p^a and k0=F_q, exactly the finite-field notation the application paragraph takes from it. Its more restrictive adic category is not used to construct the general Lambda-module sheaf. There are no proof steps to check under C1 or C4: the single construction is a definition, and the equal sign L_(Psi,b)=b^*L_Psi is exactly the existing definition, not a theorem inferred from a torsor comparison. I opened `def-fd-artin-schreier-sheaf.json` and read both its older statement and its controlling blueprint_update. The latter allows an arbitrary commutative coefficient ring with q invertible, an additive character of the finite field k, and a global function on a k-scheme. With k=F_p its cardinal is p, so the item's invertibility assumption is precisely the needed one. Our condition p=0 gives the canonical ring map F_p -> Γ(W,O) and hence W -> Spec F_p; the global function then defines W -> A^1_(F_p). Neither finite Lambda nor nontrivial Psi is required. The finite-field-specific notation at the end of that dependency does not constrain its general opening construction.

I tested W empty (the reason the Lean attachment fails), the zero coefficient ring (the unique module sheaf), p=2, trivial Psi, b=0, vector-bundle rank zero and rank one. The construction remains meaningful throughout. In rank one the evaluation polynomial is exactly x*xi; at rank zero the unique fibrewise evaluation is zero. No nonzero rank, nonempty base, compactification, finite-type condition or derived-category hypothesis was used to define this sheaf. Properties such as lissity, finite Tor amplitude and preservation of constructibility are not claimed in this definition. There are no long proof steps, hidden comparison lemmas, new-node source obligations or duplicate-tag pairs.

I ran the mandated search command for LeanFinder (two formulations), Loogle, LeanSearch and grep (AlgebraicGeometry and the whole Mathlib). The hit records in searches.jsonl were read and copied without changing queries. The first semantic search returned scheme-pullback constructions; the second returned Hilbert 90, Galois, Witt-vector and etale-locus results. LeanSearch returned analytic Fourier notation and scheme ideal-sheaf kernels. None defines this etale character sheaf, and both greps and Loogle found zero matches. No unavailable service was recorded as a negative result. I checked B-E of delivery-errors: no new statements, no inline postponed proof, no new node that duplicates a clause, no tags used in place of mathematical meaning, and no added hypothesis taken from a narrower source.

## Unfinished work

No part of the current definition remains to split. The independent maintainer review should resolve the stale stored unit text and the narrower existing Lean signature; neither file of Lean nor another node was edited.

## Dry-run repair

The first dry run exited with one finding: the realized unit did not reach its cited Fourier-conventions unit. I repaired this by retaining the existing detailed definition def-fourier-set as a statement dependency and citing its finite field k0=F_q in the application. Its stmt_deps is empty, so it does not recreate the cyclic sketch conventions. The general coefficient-ring definition is unchanged.
