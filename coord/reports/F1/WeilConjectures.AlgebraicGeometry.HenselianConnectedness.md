## What changed

Completed `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus` in
`WeilConjectures.AlgebraicGeometry.HenselianConnectedness`, preserving every existing
signature and visibility. Added only proof imports:

- `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`;
- `Sheaf.RingTheory.HenselianPairPrimeConnected`;
- `Sheaf.RingTheory.IntegralOverHenselianPair`.

Construct the closed subscheme from the vanishing ideal of C, transport irreducibility
through its closed embedding, and apply the existing general affine Stein theorem.
Its connected fibres imply surjectivity, so Spec of its global sections is irreducible.
The nilradical is therefore prime. Integral extension makes the extended ideal henselian;
the existing prime-connectedness theorem gives connectedness of its zero locus.
Mathlib's closed quotient criterion pulls this connected set back, and its continuous
image is exactly the required intersection. No arbitrary existential witness is chosen
for a definition: the subscheme, morphisms, algebra structure and extended ideal are
explicit constructions. The result includes nonemptiness without using the independent
nonemptiness lemma.

The proof compiled cleanly through lcompile.py. Mathlib searches were run through
msearch.py (LeanFinder, Loogle and grep; searches.jsonl records their actual results).
Checked the three new imports individually with import_direction.py; each is acyclic.
Updated both node copies' proof, proof_deps and proof_origin to record the Lean route.
The unit's realized statement and steps are preserved. The three existing nodes of
sk-thm-p1 are used as tools for the same Stein route, not to replace the unit argument.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`
(node `thm-weil-pbc-stein-inputs`). This is a complete Lean proof from existing named
statements, not an axiom-free completion of all its dependencies.

No sorry remains in the item's module. No new sorry, theorem, module or node was added.
The two already completed proofs (Noetherian Stein finiteness and the spectral/closed/
connected packaging), and the independent nonemptiness theorem, are retained.

Existing imported obligations used by this proof remain:

- `AlgebraicGeometry.Scheme.Hom.steinFactorization_affine`
  (`lem-weil-pbc-stein-factorization-affine`);
- `henselianRing_of_isIntegral`
  (`lem-weil-pbc-integral-over-henselian-pair`);
- `PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian`
  (`lem-weil-pbc-henselian-pair-prime-connected`).

The unchanged finiteness proof also continues to use the existing direct-image
cohomology obligations. This delivery makes no claim to close those imported holes.

## No longer needed

No module is claimed to leave the targets' import closure. The second reader changed
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism` to a plain
proof import: it is used only in the finiteness proof, never in a public signature. Trial proof imports of Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
and Mathlib.Topology.Connected.Clopen were removed: the required declarations are already
available through the retained imports. No new module or node was necessary.

For the connectedness proof, the Noetherian finiteness clause and approximation chain
are unnecessary: the general Stein theorem supplies an integral algebra directly.
Thus this argument does not need `lem-weil-pbc-etale-finite-data-descent` or
`lem-weil-pbc-etale-section-continuity` for connectedness. They remain in the node's
statement dependencies, since its textual discussion is unchanged.

For the spectral packaging node's actual proof,
`lemma-weil-pbc-spectral-restriction` and `lem-weil-pbc-closed-immersion-products`
are unnecessary: it packages the hypotheses of the criterion rather than applying it,
and closedness follows directly from continuity and the zero locus being closed.
They are removed from that node's proof dependencies, not deleted from the library.
`def-weil-pbc-henselian-terminology` and `def-weil-pbc-scheme-conventions` also
leave the packaging node's old proof_deps: they describe the unchanged statement,
not additional proof steps, and remain in stmt_deps. These four entries are the
complete difference between that node's old and new proof_deps. The primary node
had empty proof_deps, so it has no removed dependency.
The scheme-sobriety/prime-image step of the longer Stacks route is avoided by
surjectivity of the Stein map and the prime nilradical of its target.

## Where the brief, the DAG or earlier work was wrong

The primary node had no proof steps or proof dependencies despite the remaining hole.
Existing statements from the other henselian comparison route already supply all the
non-elementary inputs needed. Its new proof records those dependencies explicitly.

The packaging node's old plan used finite Stein factorization over an arbitrary base
and applied a sheaf criterion; its recorded Lean theorem only assembles spectrality,
closedness and connected intersections. Noetherian finiteness stays in its separate,
unchanged theorem and is not required for connectedness. Neither the node statements
nor their lean records were changed. The discrepancy in the packaging node's textual
statement (which discusses general finiteness and a sheaf comparison not asserted by
this declaration) is reported here rather than silently corrected.

Read Stacks Tags 0A0B and 03H2 online. The implemented route follows the closed-subscheme
reduction, integral Stein factorization and connected-fibre quotient argument of 0A0B.
Edge cases need no extra assumptions: an empty C is excluded only by its existing
IsIrreducible hypothesis; a zero base ring has no such nonempty proper source. No
Noetherian assumption, nontrivial-ring assumption or strengthened hypothesis was added.

## Second reading by F1

1. **Signatures and visible data: pass.** Compared the only delivered Lean module
   with the repository by `diff -u` and the declaration parser. All four existing
   signatures, visibility, docstrings and definitions are byte-for-byte unchanged;
   only the connectedness proof and imports differ. No new declaration or module exists. The import-visibility correction is
   recorded in coord/changes/HenselianConnectednessProofImport.md. Corrected the existing public import of
   `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism` to a
   plain import, since its declarations occur only in the finiteness proof.

2. **Proof and trust: pass, relative to existing obligations.** Independently
   compiled the delivered module through lcompile.py. A scratch copy prints the
   axioms of all four theorems: finiteness, connectedness and spectral packaging
   use only `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`; independent
   nonemptiness uses only the three permitted foundational axioms. No local sorry,
   axiom, unsafe, opaque, implemented_by, extern or holed definition occurs.
   The three imported obligations remain open and are explicitly listed above.
   The closed subscheme, canonical ring map and extended ideal are constructed;
   no arbitrary data is chosen from an unproved existence theorem.

3. **Split statements: pass (none added).** Read the actual signatures and
   docstrings of SteinFactorizationAffine, HenselianPairPrimeConnected and
   IntegralOverHenselianPair and checked Stacks 03H2, 09Y6 and 09XK. The composite
   of the closed immersion with p is proper; the Stein theorem applies without
   Noetherianity. Its singleton inverse images are connected and nonempty,
   yielding surjectivity. Irreducibility transports first across the closed
   embedding, then across this surjection; hence the nilradical is prime.
   The integral algebra instance has exactly the canonical map required by the
   integral-henselian theorem. Applying prime connectedness to the nilradical
   and using V(nilradical) = univ gives the required connected V(K).
   Empty C is excluded by IsIrreducible, and zero rings give no nonempty source
   over their empty spectra; I = 0 gives the connected irreducible C itself.
   There is no split-off restatement of the item. Independent rg searches on
   lean/ and Mathlib confirmed the existing closed-subscheme construction,
   prime-nilradical criterion and quotient-preimage lemma; no extra lemma is needed.

4. **Shortest route, imports and unit: pass after import/report repair.** Read
   Stacks 0A0B and dag/units/sk-thm-iff.json. The argument retains the Stein and
   henselian-connectedness route of the unit; its realized statement and step
   remain lemma-weil-pbc-property-iff-acyclicity. The use of existing tools from
   sk-thm-p1 does not replace a unit step. Mathlib's
   Topology.IsCoinducing.isConnected_preimage_of_isClosed supplies exactly the
   closed-connected-set pullback with connected fibres. The explicit factorization
   identity and spectrum comap formula identify the pulled-back zero locus;
   the image-preimage/range equality identifies its image with the original
   intersection. No Noetherian finiteness or approximation is required here.
   All three new proof imports supply declarations actually used. Corrected the
   public proof import and completed No longer needed with the two missing
   definitional entries from the packaging node's old proof_deps.

5. **DAG consistency: pass.** Opened both delivered node files and their originals.
   Only proof, proof_deps and proof_origin change. The primary node records the
   unchanged finite-direct-image proof and each actual connectedness step,
   including the Mathlib closed-subscheme and quotient-preimage matches. The
   packaging node records compactness/quasi-separatedness, closedness by
   continuity and the connectedness theorem, with proof_deps exactly the union
   of step uses. No new node is needed. The pre-existing mismatch between the
   packaging node's broad informal statement and its narrower Lean packaging
   remains reported above, not silently altered or claimed proved.

Second-reading changes: made DirectImage.AffineMorphism a plain proof import;
completed the pruning inventory for the packaging node. The mathematical proof
required no repair.

Import correction change record: `coord/changes/HenselianConnectednessProofImport.md`.
The first dry run required this record; the 205 downstream modules are inventoried
there. No existing statement or definition is altered and no adaptation is needed.

Validation of the visibility correction: compiled the delivered module into its
sandbox overlay through lcompile.py --all, then compiled unchanged scratch copies
of HenselianClopenRestriction (5.9 s), DegreeZero (9.1 s) and Gabber (54.3 s) against
that overlay. All compiled cleanly. The aggregate WeilConjectures module directly
public-imports DirectImage.AffineMorphism, so its exported API retains that import.
The repaired dry run printed OK; review class CODEX (node changes and documented
public-import correction).
