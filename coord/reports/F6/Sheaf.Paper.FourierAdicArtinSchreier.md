## What changed

In `Sheaf.Paper.FourierAdicArtinSchreier`, proved the unique integral character lift,
proved invertibility of the characteristic prime, and constructed an explicit etale
cover trivializing the integral Artin--Schreier sheaf. The cover is the pullback of
the universal Artin--Schreier etale surjection. Its trivialization uses the existing
`Etale.artinSchreierSheafUpperStarIso` and inverse-image composition isomorphisms.

The membership proof now combines this cover with two separately stated integral-line
results: canonical derived completeness and constructibility of all positive derived
reductions with the fixed support interval [0,0]. They are private proof imports;
all existing public signatures and all object constructions are unchanged. The
new modules retain the actual constant-to-completion scalar extension, quotient
functors, units and coefficient universes.

Validation: `lcompile.py --all` compiled all three modules in dependency order,
with exit code 0 (8.4 s, 12.1 s and 44.6 s). The explicit coefficient arguments in
the reductions statement avoid expensive inference of the support predicate.

## Proved and sorry left

Original module: three holes closed, zero local holes left.

- `WeilConjectures.fourierIntegralCharacter_existsUnique`: proved.
- `WeilConjectures.fourierIntegerPrime_isUnit`: proved.
- `WeilConjectures.fourierAdicArtinSchreier_mem`: reduced to the two results below,
  with a complete Lean proof of its Artin--Schreier trivialization and assembly.
  This is a decomposition, not a claim that its dependency closure is sorry-free.

Two new holes, each a public theorem with its own source, proof in words and node:

- `WeilConjectures.etaleIntegralLine_derivedComplete`
  (`lem-fd-etale-integral-line-derived-complete`), in
  `Sheaf.Paper.EtaleIntegralLineDerivedComplete`.
- `WeilConjectures.etaleIntegralLine_reductions`
  (`lem-fd-etale-integral-line-reductions`), in
  `Sheaf.Paper.EtaleIntegralLineReductions`.

Thus two original holes are proved directly, one is decomposed, and two holes are
added. The packet has exactly two literal `sorry`s and no sorry in a definition.
Both remaining results are independent of characters and the Fourier setting.
The first concludes only completeness; the second concludes only the finite-level
condition. Neither restates the whole membership assertion. Their edge cases include
empty schemes, the trivial character, ramified coefficient extensions, and arbitrary
etale covers. A constant regular line satisfies both by the quotient-limit and
regular-module tensor calculations; the given cover provides their descent.

## No longer needed

No existing imports, nodes or modules are pruned. The original node had no recorded
proof dependencies. The revised node records the arithmetic, existing Artin--Schreier
trivialization and the two integral-line results actually used. No finite-dimensional,
separatedness or additional invertibility hypotheses are introduced through a lisse
realization theorem. The nearby modules `LisseIntegralCompletedRealization`,
`LisseCompletedSystemComparison` and `IntegralStratifiedPerfectCharacterization` are
not imported: their hypotheses do not cover this statement for every Noetherian X.
The constant-object theorem alone does not supply descent or an identification of
this actual scalar extension, so it is also not imported.

## Where the brief, the DAG or earlier work was wrong

The original definition node had an empty proof plan and dependency list despite
its nontrivial intrinsic membership assertion. The delivery records the argument
and its two general ringed-site obligations. Existing local-system equivalences
supply ordinary quotient towers, but do not directly state completeness for the
specified derived quotient units of this completed scalar extension.

The earlier report incorrectly described the cover proof as unverified scratch work
and the membership hole as untouched. Both have since compiled in the delivery
module. Earlier compiler connection failures were transient; the current complete
packet compiles successfully. Provider interruptions also reset the reference clock:
the earlier recorded start was 1792425882.9888, while the resumed sandbox start is
1792438080.743162. The budget files were not edited.

## New nodes

`lem-fd-etale-integral-line-derived-complete` isolates the canonical Roos triangle
for the completed scalar extension of an etale-trivial integral line. Its source is
Bhatt--Scholze Lemma 6.8.2(1), Proposition 6.8.4(1) and Section 3.5. Its statement
keeps the actual quotient units, rather than merely asserting existence of an
unrelated homotopy-limit object.

`lem-fd-etale-integral-line-reductions` isolates the K-flat ordinary/derived quotient
comparison and finite locally constant cohomology in degree zero. Its source is
Bhatt--Scholze Proposition 6.8.4(1), Corollary 5.1.5 and Section 6.5. It supplies the
uniform interval [0,0] needed by the parent and imposes no Tor-amplitude hypothesis
on unrelated inputs. No change record is needed: no existing signature or definition
is changed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
