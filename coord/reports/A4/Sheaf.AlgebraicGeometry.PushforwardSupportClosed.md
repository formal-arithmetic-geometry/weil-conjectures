## What changed

Proved `AlgebraicGeometry.pushforward_support_closed_subset` in
`Sheaf.AlgebraicGeometry.PushforwardSupportClosed`, with its signature and public imports
unchanged. Added proof-only imports of `CoherentFiniteTypeLocallyNoetherian` (with `all`
for its proved private local-presentation helper), `FiniteTypeModuleSupportClosed`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.

Finite local generators and their finite-type kernels give finite presentation of the
coherent input. This conversion is expressed generically inside the proof to keep the
concrete scheme sheaf out of expensive unification. Existing proper higher-direct-image
finiteness and quasi-coherence in degree zero transfer across `rightDerivedZeroIsoSelf`.
The existing finite-type support theorem then supplies the closed subset D. The containment
is proved directly: outside the closed image q(C), source stalks are subsingleton, sections
are equal by germ extensionality, and arbitrary target germs become equal after restricting
to a common neighbourhood.

Updated the item's DAG proof, dependencies, and proof origin to describe this argument.
The unit's realized statements and steps are unchanged. Consulted Stacks Tags
[088E](https://stacks.math.columbia.edu/tag/088E) and
[02O5](https://stacks.math.columbia.edu/tag/02O5) online because the local source documents
are absent. Search through LeanFinder, Loogle, Mathlib source, and both project roots found
no existing general pushforward-support theorem.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.pushforward_support_closed_subset`
(node `new-chow-pushforward-support-closed`).

The item's module has no remaining `sorry`. Added zero holes, zero new theorems with
`sorry`, and zero new nodes. This is a complete proof from existing library declarations,
not a decomposition into new holes. Its existing proper higher-image dependencies still
have their own unproved inputs; they are not claimed to be axiom-free here.

The final single-file compile passed without errors or warnings, within the 60-second limit.
The proof includes empty source/target and zero input without nonemptiness assumptions;
section extensionality also handles the empty open.

## No longer needed

No original import or planned proof-dependency node is pruned. All three originally planned
nodes remain needed; the DAG additionally records the existing higher-image quasi-coherence
statement, coherence definition, proper-morphism definition, module-stalk definition, and
Mathlib germ-extensionality leaf.

An exploratory proof used the private finite-presentation helper of
`Sheaf.AlgebraicGeometry.ProjLineSerreVanishing`; that import was removed from the final
proof so its unrelated theory is not brought into the closure by this delivery.
No closed-immersion stalk theorem or new general support-containment lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The plan's coherence input is recorded in Lean as finite
presentation of higher direct images, rather than a theorem returning RingedSpace.IsCoherent
for ordinary pushforward. The implementation therefore supplies finite presentation of the
input, uses degree zero, and transports across the canonical underived comparison.
Quasi-coherence of higher direct images is separately stated in
`lem-pc-sections-higher-direct-image-quasi-coherent`; the original dependency list did not
name it. The formerly uncited stalk-containment argument is now fully written in Lean and
its Mathlib germ-extensionality and stalk-representative inputs are recorded in the DAG.

## Second reading by A4

1. **Interface preservation — pass.** Compared the entire delivered Lean module and node
   with the read-only repository using `diff -u`. The existing theorem signature, docstring,
   universe, namespace, visibility, and both public imports are byte for byte unchanged.
   The only Lean additions are the proof and three non-public proof imports. No definition
   or statement changes, adaptations, or change records are needed.
2. **Proof and axioms — pass.** Independently compiled the delivered module with
   `lcompile.py`: no errors or warnings, 21.1 seconds. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.pushforward_support_closed_subset`: exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from existing open
   dependencies, including `isQuasicoherent_higherDirectImage`; no local hole remains.
   Read the finite-generator reindexing, kernel presentation helper, degree-zero comparison,
   support construction, section extensionality, and germ restriction argument. There are
   no forbidden declarations, hollow definitions, or arbitrary data witnesses obtained
   from an unproved existence theorem. D is constructed directly from its support set.
3. **Split statements and edge cases — pass.** No statements or nodes are split off, and
   no new holes are added. The finite-presentation argument uses finite generators with
   a finite-type kernel, rather than assuming the desired conclusion. Zero ranks, the
   zero module, empty opens, and empty schemes require no extra nonemptiness hypothesis.
   In particular, section extensionality on an empty open is vacuous and valid; the
   common neighbourhood U ∩ W contains the point whenever stalk representatives are used.
4. **Shortest route, imports, pruning, unit — pass.** Independently searched with
   LeanFinder for zero direct-image stalks outside a closed support image, Loogle for
   pushforward quasi-coherence, `msearch.py grep`, and `rg` in both project roots and
   Mathlib. The ideal-sheaf support results and canonical stalkPushforward map do not
   prove the general module assertion. Mathlib's quasi-coherence pushforward criteria
   require extra site-functor hypotheses and do not replace the proper-image theorem.
   Existing local finite-presentation and twisted-section modules do not offer a shorter
   public conversion; the latter's private conversion brings unrelated theory, while
   this proof reuses the already proved kernel-presentation helper. Each new proof import
   is used. All three old proof dependencies remain used, so `No longer needed` is
   complete. Read `dag/units/sk-thm-p1.json`: this is a subordinate support lemma, not a
   realized unit statement or step; the unit route and its realized nodes stay intact.
5. **DAG agreement — pass.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Its five steps follow the Lean argument, and their uses have exactly
   the listed union. Checked the existing coherence, higher-image, finite-type support,
   germ-extensionality, proper-morphism, and stalk records against the declarations used.
   No existing statement or source was altered, and there are no new-node fields to check.

Second-reading changes: appended this independent review and its compiler/axiom evidence.
No repair to the Lean proof or DAG was necessary. Confirmed one original hole closed,
zero holes added, and no planned dependency pruned; this does not assert an axiom-free
transitive proof of the target while its existing inputs remain open.
