## What changed

Reduced `AlgebraicGeometry.adjoint_tensor_annihilator_transport` without changing its
signature or existing docstring. The proof constructs the explicit tensor object and map,
applies the projection factorization, and proves zero precomposition by adjunction
naturality and preservation of zero. Additivity of F follows from hF and the proved
additivity of unbounded derived direct image, reflected through the faithful inclusion.

Added proof-only imports of `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen`,
`Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionProjection`,
`Mathlib.CategoryTheory.Adjunction.Additive`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive`.
The two new modules each state one geometric part of the original proof. The first
has no direct image or adjunction. The second has no right adjoint, beta, Q, open,
restriction assumption or killing hypothesis. They share the explicit construction
using `derivedPullbackAcrossUniverses`, avoiding arbitrary existential object choices.

Updated the original node's proof, proof_deps and proof_origin to the actual combination.
Every delivered Lean module compiled independently with lcompile.py; sibling modules
were compiled in import order. No existing interface or target statement was changed.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.adjoint_tensor_annihilator_transport`
(node `lem-sc-adjoint-tensor-annihilator-transport`). No sorry remains in the item's module.
This is a decomposition, not a complete proof free of sorry dependencies: one upper
hole closed and two lower holes added, giving a textual net of minus one for this packet.

The two remaining sorries added by this delivery are exactly:

- `AlgebraicGeometry.exists_derivedTensor_precomposition_open`, node
  `lem-sc-derived-tensor-precomposition-open`, in
  `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen`.
- `AlgebraicGeometry.exists_derivedTensor_precomposition_projection`, node
  `lem-sc-derived-tensor-precomposition-projection`, in
  `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionProjection`.

Each is a public theorem whose whole proof is `by sorry`; each carries its source,
complete natural-language argument and blueprint marker. No definition was added.
The parent theorem's categorical deduction compiles from exactly these statements.

## No longer needed

No existing import was removed, and no globally pruned module is claimed.
All original public imports support the unchanged statement and visibility.
The parent no longer directly depends on `lem-pc-projection-formula`,
`lem-pc-derived-pullback-tensor-qcoh`, or
`lem-pc-affine-derived-pullback-tensor-tilde`; its direct proof dependencies are the
two new nodes. The last two remain geometric inputs of the new open-map node.
The invertible-module higher-direct-image declaration attached to
`lem-pc-projection-formula` is not imported or used. The new projection node instead
plans the perfect-duality argument for the canonical map, retaining the unit's route.

## Where the brief, the DAG or earlier work was wrong

The node's first proof step asks for a natural derived projection square, but
`lem-pc-projection-formula` is attached to
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`.
That declaration concerns an invertible module and one higher-direct-image degree;
it supplies neither the unbounded perfect-complex formula nor its naturality and unit
compatibility. `nonempty_qcqs_derivedProjection_iso_universes` supplies an object
isomorphism only, with a shared universe; it cannot determine the required square.
The existing pullback/tensor and affine restriction declarations also have shared
universe binders, while this item's statement has independent wX and wY.
The new lemmas isolate precisely the missing geometric interfaces rather than assume
that an arbitrary object isomorphism is the canonical projection formula.

The projection lemma allows any unit isomorphism e. Its docstring accounts for that
choice explicitly: compare e with the canonical unit e0, act on P by their ratio,
and move F of that automorphism through i tensor identity by tensor naturality.
Thus the first lemma need not specify a canonical e to make the second applicable.
Zero P, zero i, identity i and empty V cause no extra hypotheses. In particular,
zero i can satisfy the restriction condition only where its localized domain and
unit are zero; the proof uses the actual IsIso assumption, not nonvanishing.

Mathlib searches were run through msearch.py and recorded in searches.jsonl.
LeanFinder returned ordinary module pullback unit identities and Tor naturality,
not either new statement. Loogle returned the generic adjunction Hom equivalence.
Mathlib grep found no derived scheme formula. LeanSearch returned an internal server
error and is recorded as unavailable, not as proof of absence. Library searches also
checked DerivedPullbackAcrossUniverses, DerivedPullbackOpenRestrictionUniverses,
DerivedTensorQCohClosure, PerfectTensorHomDuality, the monoidal models and the
right-adjoint tensor projection modules; their signatures do not state these two
independent-universe conclusions.

The local clone lacks the ignored Stacks TeX checkout although literature/LIST.md
records it as obtained. The mathematical source was read online instead:
https://stacks.math.columbia.edu/tag/0E4G (Lemma 48.4.4, final paragraph),
https://stacks.math.columbia.edu/tag/08EU (canonical projection formula), and
https://stacks.math.columbia.edu/tag/08DW (pullback preservation and restriction).
New proof_origin entries mark the expanded arguments as agent-written.
The unit record `sk-thm-picard-duality` has empty realized arrays, and no unit statement
or unit proof step is bypassed or changed. Blueprint and DAG searches found no existing
node with either new precise statement. The original node already points to
`lem-sc-finite-duality`; that ancestry is preserved for both new nodes.

## New nodes

`lem-sc-derived-tensor-precomposition-open` states quasi-coherence and open invertibility
of the explicit map `(Lf*i tensor id);(e tensor id);lambda`. It splits the geometric
construction and restriction part of the parent, with no F, a, beta, Q or hkill.
Its Lean module is `lean/Sheaf/AlgebraicGeometry/DerivedTensorPrecompositionOpen.lean`.

`lem-sc-derived-tensor-precomposition-projection` states a factorization of the underlying
F.map of that explicit map through `(i tensor id);lambda`. Its mathematical argument is
the canonical perfect projection formula with unit coherence, transport through hF,
and correction for the arbitrary supplied unit isomorphism. It has no adjunction or
annihilation hypothesis and does not assert any killing conclusion. Its module is
`lean/Sheaf/AlgebraicGeometry/DerivedTensorPrecompositionProjection.lean`.

There are no change records or forced adaptations: all existing signatures and
visibility stay identical.

## Second reading by S1

1. **Interfaces and visible data — PASS.** Read the three delivered modules in full and
   compared the parent with the repository using `diff -u`. Its sole existing declaration,
   `AlgebraicGeometry.adjoint_tensor_annihilator_transport`, has a byte-identical signature
   and unchanged docstring. The only Lean changes are four proof-only imports and the proof
   body. There are no definitions, interface changes, change records or forced adaptations.
   Comparison of the parent JSON finds changes only in `proof`, `proof_deps`, `proof_origin`.

2. **Kernel check and holes — PASS as a decomposition.** Independently compiled all three
   files in import order with `lcompile.py --all`: no errors or warnings. Compiled a scratch
   copy with `#print axioms` for all three theorems: each reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. There are no forbidden declarations or
   escapes. The parent's two `obtain`s use the geometric statements as propositions in a
   proof, not as arbitrary data in a public definition. Its explicit R and j agree with both
   helper conclusions. Associativity and hkill prove F(j);alpha=0; faithful inclusion and hF
   transfer additivity, and source naturality and `homAddEquiv_zero` prove j;beta=0.
   One original hole is closed and exactly the two named helper holes listed above are added;
   no claim of a sorry-free proof or positive net progress is made.

3. **Split statements, sources and edge cases — PASS.** Read Stacks 0E4G, Lemma 48.4.4,
   final paragraph, and 08EU, 08DW, 08DX online. The open helper is only the explicit
   construction, quasi-coherent closure and restriction calculation: it has no F, adjunction
   or killing hypothesis. The projection helper is only the direct-image factorization,
   with no V, beta, Q or annihilation conclusion. They are separate strict parts of the
   source argument, not relabelings of the parent. The source's support and boundedness
   assumptions on Q belong to finding i, which is already supplied here; they are not used
   by either helper. Properness gives the qcqs hypotheses required by the projection helper.
   Neither properness nor flatness is needed for the open helper.

   Checked the potentially delicate arbitrary e: if c=e0.inv;e.hom and
   d=lambda_P.inv;(c tensor id_P);lambda_P, then j=j0;d. Taking
   t=t0;(id_I tensor F(d)) gives t;(i tensor id);lambda=F(j0);F(d), by tensor and
   unitor naturality. This works for any unit automorphism, not only the canonical choice.
   For identity f and i, this reduces to the unit-action formula. For zero P both
   constructions are zero-object calculations. For zero i, j is zero and the factorization
   holds; the open hypothesis then forces the restricted unit and domain to be zero.
   Empty V makes the restriction assertion automatic. No nonempty-open, bounded-P,
   quasi-compact-V, or nonzero-map assumption was introduced.

   Both helpers have complete prose proofs, source and blueprint markers, and matching
   new nodes. Ran additional msearch queries using `tensor.*counit|counit.*tensor|unit.*pullback`
   (grep), monoidal adjunction/dualizable projection normalization (LeanFinder), and
   `CategoryTheory.Adjunction.homEquiv, 0` (Loogle). The results give underived unit facts,
   rigid evaluation identities and the exact additive Hom-equivalence lemma used by the
   parent, but not the geometric independent-universe helpers. Also searched repository
   Lean, DAG nodes and upstream algebraic geometry. Read the proved categorical theorem
   `CategoryTheory.monoidal_projection_conjugate`, the pinned projection theorem, perfect
   tensor-Hom duality, canonical tensor QCoh closure, and both restriction interfaces.
   The pinned projection theorem imposes Noetherian/proper and shared-universe assumptions;
   the object-only qcqs isomorphism does not specify the required natural square.
   Closing either helper still requires the localization/tensor/restriction coherence
   transport, not a short application of an existing exact statement.

4. **Top-down route, imports and pruning — PASS.** The parent's proof uses exactly the two
   geometric reductions, then standard additive adjunction glue. Its old three direct
   proof dependencies are all accounted for in `No longer needed`; the pullback and affine
   restriction nodes remain inputs of the open helper, and the invertible-module projection
   formula is not used. No global module pruning is claimed. All original public imports
   support the unchanged signature (including its proper/flat/finite-presentation binders);
   all added parent imports are proof-only and used. The new public imports support their
   new signatures. Read `dag/units/sk-thm-picard-duality.json`: its realized statement and
   step arrays are empty. No unit route, statement or realized node has been altered.

5. **DAG agreement — PASS after repair.** Checked each verbatim `lean.statement` against its
   file, all proof-dependency unions against step `uses`, and the parent combination against
   its three steps. The new nodes have their chapter/unit, source, searches, origin, creation,
   blueprint ancestry and Lean records. Found one missing citation in the projection node:
   identifying the canonical projection mate with the conjugate of a tensorator was stated
   without citing the existing theorem that proves this normalization. Added
   `lem-sc-monoidal-projection-conjugate` to step 1 and `proof_deps`, and rewrote that step to
   apply its exact statement to the mapped perfect pairing. The inverse canonical mate
   supplies t0; naturality, unit coherence, hF and the arbitrary-e correction supply the
   remaining steps. This keeps the same geometric argument and adds no new statement or hole.

Changes by this reader: repaired that projection DAG citation and step, added this review,
and preserved all Lean files. Scratch axiom-check source is kept outside the delivered
`lean/` tree. The delivery is a one-to-two decomposition, not a completed geometric proof.
