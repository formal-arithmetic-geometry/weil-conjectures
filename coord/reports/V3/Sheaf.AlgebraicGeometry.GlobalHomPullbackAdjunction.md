## What changed

Replaced the earlier attempt with a decomposition through a fixed, explicitly constructed
pullback-counit map. The existing theorem signature and public imports are unchanged.

`GlobalHomPullbackCounitIsomorphism.lean` defines
`AlgebraicGeometry.schemeGlobalHomPullbackCounitMap` by composition of the recorded pullback
comparison and global Hom of the fixed counit. No data is chosen from a new existence theorem.
Its one open theorem states componentwise invertibility and naturality.
`GlobalHomPullbackCounitHZero.lean` states the independent degree-zero calculation, including
existence of compatible additive identifications. Each new module has one open statement.

In `GlobalHomPullbackAdjunction.lean`, the proof obtains the two independent facts, uses
`asIso` and `NatIso.ofComponents` to assemble the natural isomorphism, and proves its
factorization by reflexivity. The H⁰ clause follows from the second fact because the constructed
components are definitionally the fixed composite. The original DAG node now records this route.

Validation: all three modules compiled together using lcompile.py; deliver3.py --no-push
printed OK, with only the second reading deferred to the next worker as required. Both remaining holes are
entire named public theorem proofs. No existing statement, definition or visibility was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeGlobalDerivedHom_pullback_adjunction`
(node `lem-pc-global-hom-pullback-adjunction`) by decomposition.

Two new holes remain:

- `AlgebraicGeometry.schemeGlobalHomPullbackCounitMap_isIso_natural`
  (`lem-pc-global-hom-pullback-counit-isomorphism`).
- `AlgebraicGeometry.schemeGlobalHomPullbackCounitMap_hzero`
  (`lem-pc-global-hom-pullback-counit-hzero`).

This closes one upper hole and adds two lower holes; it is a decomposition, with declared-hole
change +1, not a sorry-free proof of the mathematical result. The first lower claim contains
no H⁰ identifications or compatibility clause. The second contains no invertibility assertion
or natural isomorphism. Neither is the target under a new name.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction`
  (`lem-pc-derived-internal-hom-pullback-adjunction`).
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom` (`def-pc-global-derived-rhom`).
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`
  (`lem-pc-ringed-spaces-derived-adjoint-general`).
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
  (`lem-pc-ringed-spaces-derived-direct-image-composition`).

The public imports `GlobalHomPullbackComparison` and `RhomGlobalSections` are retained to
preserve the existing exported interface. GlobalDerivedHom remains transitively needed for
the statements. The direct ringed-space adjunction/composition interfaces are replaced by the
pinned adjunction and Leray data already present through GlobalHomPullbackComparison; no claim
is made that these modules are globally unreachable. The internal-Hom theorem's existential
witnesses are not used: they do not state equality with those pinned constructions.

Removed the earlier sandbox module `GlobalHomPullbackAdjunctionData.lean` and the proposed
nodes `lem-pc-global-hom-pullback-adjunction-data` and
`lem-pc-global-hom-pullback-adjunction-hzero`. They never entered the library and are not delivered.
The item imports only the new H⁰ module privately; its public import of the new
isomorphism module makes both lemmas available. Redundant direct imports of the new
isomorphism module and RhomGlobalSections in the new H⁰ module were removed.
No other new proof import is unused.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's `globalHomPullback_hzero` quantified over arbitrary GlobalHomPullbackData,
whose additive equivalences were unconstrained. This is false in general: even for an identity
morphism, independently negating one H⁰ identification changes the induced correspondence
on a nonzero group of characteristic different from two. A concrete test case is the identity
of Spec Z and the structure sheaf in degree zero. The replacement asserts existence of compatible
identifications for a fixed map, rather than compatibility for arbitrary identifications.

The earlier nodes copied unrelated review/audit history and had no self-contained mathematical
statements or complete proof docstrings. They are replaced entirely, and the earlier worker's
purported second reading is removed; the actual second reader must provide that section.

The earlier search records had LeanFinder and Loogle, which count as one search kind, and
omitted LeanSearch. Actual new searches were run via msearch.py. LeanSearch returned HTTP
Internal Server Error and is recorded as unavailable. LeanFinder returned underived sheaf
pullback facts, grep found no global derived-Hom adjunction, and Loogle found the generic
NatIso.ofComponents assembly tool. Local source searches found the related global Hom right
adjunction theorem, but its qcqs right-adjoint statement does not match this arbitrary-morphism
pullback adjunction. The internal-Hom theorem gives existential adjunction/tensor data, not
identifications with the fixed data defining the public pullback comparison; direct application
of it does not establish the required pinned factorization. The new first lemma isolates that
canonical-mate argument instead of silently identifying unrelated witnesses.

Sources 079W, 08I3 and 0B6A were read at their Stacks Project tag pages because the literature
TeX files are absent on this machine. The proof descriptions in the two new modules explain
the tensor-Hom/Yoneda argument and the representative H⁰ computation. Identity morphisms,
zero inputs and empty schemes introduce no extra hypotheses or exceptions. The unit record
sk-thm-picard-duality has no realized steps or statements at this node, and its route is unchanged.

## New nodes

`lem-pc-global-hom-pullback-counit-isomorphism`, in
`GlobalHomPullbackCounitIsomorphism.lean`, isolates the invertibility and naturality of an
explicit map. Its proof uses tensor-Hom adjunction, the fixed pullback adjunction and tensor
comparison, Yoneda and the fixed Leray isomorphism. The construction has no H⁰ content.

`lem-pc-global-hom-pullback-counit-hzero`, in `GlobalHomPullbackCounitHZero.lean`, isolates
the H⁰ action of the same explicit map. Its proof uses the K-flat/K-injective computation,
exact scalar restriction and evaluation-mate compatibility. It supplies no complex-level
invertibility or natural-isomorphism claim. The source, mathematical statement, full proof
plan, real searches and blueprint ancestor are recorded in each node. No change record is
needed: only the existing theorem's proof and private proof imports changed, and the new
modules introduce new declarations without adapting an existing interface.

## Second reading by V3

1. **Statements and interfaces.** Compared the delivered item with the repository version. The
existing theorem signature is byte-for-byte unchanged; the two added modules contain only the
recorded split statements and the fixed construction used by them. Verdict: pass.
2. **Proof and axioms.** Compiled all three modules with `lcompile.py`; there are no errors,
forbidden declarations, or sorries in definitions. The two remaining sorries are named public
theorems with complete proof docstrings and matching DAG nodes. Verdict: pass, with the two
declared split holes remaining.
3. **New statements.** Checked that the isomorphism/naturality statement and the independent H⁰
compatibility statement are strictly simpler than the target and do not restate it. Their sources,
proof plans, searches, and Lean declarations agree with their node files. Verdict: pass.
4. **Pruning and route.** The item removes only proof-only imports listed above; retained public
imports are needed for the exported statements. The proof uses the fixed counit construction,
`NatIso.ofComponents`, and the two split lemmas. The unit route and `realized` record are unchanged.
Verdict: pass.
5. **DAG agreement.** Compared declarations, proof dependencies, origins, and node metadata with
the Lean code. The target node records the two split dependencies, and each new node records its
declaration and blueprint ancestor. Verdict: pass.

I changed only this report section after the first worker delivery; no Lean proof or statement was
changed during second reading.
