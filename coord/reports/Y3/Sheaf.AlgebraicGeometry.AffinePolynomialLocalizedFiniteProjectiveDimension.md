## What changed

Replaced the sole sorry in
`AlgebraicGeometry.affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise`
by a complete proof with an explicit split on whether the prime contains the presentation
kernel. Outside the kernel support, an inverted kernel element annihilates every module
element. The localized-module subsingleton criterion proves that the localization is zero,
and its projective dimension is at most zero.

On the support, construct the surjective R-linear map R → B, deduce finite generation,
and localize it. The affine base is Noetherian by its affine-open property. Combine a
stalk-to-localized Tor bound with a general criterion for finite modules over localized
polynomial rings. These are two new proof-only imports, each with one public theorem,
one named sorry, its source, a complete proof in words, and its DAG node. The parent
node now records the argument actually used. Existing signatures and visibility are
unchanged; no definitions or instances were added.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise`
(node `lem-pc-affine-polynomial-localized-finite-projective-dimension`). The parent has
no remaining sorry. This is a decomposition, not a sorry-free proof: two holes were
added, and the net hole count changes by -1.

The two remaining sorries are:

- `AlgebraicGeometry.affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le`
  (`lem-pc-affine-polynomial-localized-tor-of-stalkwise`). This only transports the given
  stalkwise Tor bound to the supported localization over the affine base. It makes no
  projective-dimension claim.
- `ModuleCat.localizedPolynomial_finiteProjectiveDimension_of_finiteTor`
  (`lem-pc-localized-polynomial-finite-projective-dimension`). This is the independent
  algebraic step: a finite module over a localized polynomial ring over a Noetherian base
  has finite projective dimension if it has finite Tor dimension over that base. It has
  no schemes or stalkwise hypothesis.

Local compilation of all three modules and the delivery dry run check the unchanged
parent signature and the compiled combination. The two new theorems remain whole-proof
sorries as required. The zero-module and zero-variable cases were checked mathematically:
the supported-prime lemma is vacuous for a surjection onto the zero ring; the algebraic
lemma allows the zero module with bound zero and handles n = 0 by flat localization.
No arbitrary data are chosen from unproved existence theorems.

## No longer needed

No existing imports were removed, and no existing module is pruned. The four original
public imports provide the statement's schemes, stalk Tor predicate, polynomial ring,
and localized projective-dimension predicate. The parent proof no longer directly uses
`def-pc-perfect-morphism`, `def-pc-scheme`, or
`def-weil-pbc-finite-global-dimension` as proof dependencies: these notions are still
needed for its statement or the new intermediate statements. Their nodes are not globally
unneeded. No claim of pruning their modules is made.

The parent and its descendants `AffinePolynomialResolutionOfStalkwise`,
`AffineSectionsFiniteTorOfStalkwise`, and `StalkTorDimensionLocallyUniform` cannot serve
as shortcuts: their import closures already pass through this item. They were not imported.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies name definitions rather than the substantive stalk
transport or relative polynomial-ring perfection result. Those steps cannot be closed by
applying the listed declarations. The two new nodes isolate these actual steps without
changing the parent statement or bypassing a unit step. The unit
`sk-thm-picard-duality` has no realization entry naming this node; the reduction retains
the same relative finite Tor route inherited from `lem-sc-finite-duality`.

The algebraic criterion is stated over the affine base A rather than its prime
localization A_r. This is valid because the stalk's finite flat resolution over A_r
remains A-flat under flat scalar restriction. The flat map A → R_p still has polynomial
localization fibres of global dimension bounded by the number of variables. Thus Tag
068X applies directly, and the scalar restriction map in the conclusion is explicit.

Read Stacks Tags 069C and 068X online. Lean Finder returned only local projectivity and
projective-dimension reformulations for the algebraic search, and unrelated finite-type
localization results for the geometric search. LeanSearch was unavailable (HTTP internal
server error); Loogle did not recognize the unqualified projective-dimension identifier.
The grep searches found no usable exact result. Blueprint searches for `068X` and
`localized polynomial` both returned zero matches. The upstream source and the repository
were searched for an existing result and no acyclic shorter route was found.

## New nodes

`lem-pc-affine-polynomial-localized-tor-of-stalkwise`, in
`lean/Sheaf/AlgebraicGeometry/AffinePolynomialLocalizedTorOfStalkwise.lean`, records the
supported-prime affine/stalk identification and the flat scalar-restriction Tor bound.
Its precise scalar map is the polynomial constant map followed by the localization map.

`lem-pc-localized-polynomial-finite-projective-dimension`, in
`lean/Sheaf/RingTheory/LocalizedPolynomialFiniteProjectiveDimension.lean`, records the
Noetherian finite-module case of Tag 068X and the finite-projective-resolution/Ext
conclusion. Neither node restates the parent theorem: they supply separate geometric
and algebraic parts, combined with genuine finiteness and zero-support proofs in the parent.

No change records are needed: no existing public statement, definition, import or
instance changed.

## Second reading by Y3

1. Compared the delivered parent module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof text were added.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds.
The parent has no `sorry`; each split module has just its named theorem's whole-proof
`sorry`. Explicit `#print axioms` in a scratch module for all three declarations returned
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected for this
one-hole-to-two-hole decomposition. No `axiom`, `unsafe`, `opaque`, `implemented_by`,
`extern`, skip-kernel option, hollow definition or arbitrary witness construction occurs.
The delivery's own probe also checks the declarations before pushing.
3. Checked the split statements against their Lean declarations and DAG nodes, and read
[Tag 069C](https://stacks.math.columbia.edu/tag/069C) and
[Tag 068X](https://stacks.math.columbia.edu/tag/068X). Both are strictly subordinate
reductions: one transports the supported affine stalk Tor bound; the other is the
independent finite-module algebraic criterion. Restriction along A → A_r preserves flat
resolutions because localization is flat. Tag 068X applies to A → R_p: all its fibres
are polynomial localizations over fields, with global dimension at most n. For n = 0
and M = S the bound zero works; over a field A the algebraic assertion specializes to
Hilbert syzygy for finite modules over a localized polynomial ring. The zero module
has bound zero, and a surjection onto the zero ring has no supported prime. Neither
statement restates the parent. Independent Lean Finder search for flat scalar
restriction/flat dimension returned only flatness-localization criteria; Loogle search
`CategoryTheory.Tor', ModuleCat.restrictScalars` returned no hits. Ripgrep of both library
roots and Mathlib's Tor, flatness and local-projective-dimension sources found no exact
result or acyclic shortcut. These are genuine open steps; neither can be closed by a
few-minute application of an existing declaration.
4. Read the proof downward. The kernel-not-contained branch correctly makes the localization subsingleton; the supported branch uses the two split lemmas, Noetherianity, finite generation, and localization finiteness. The imports are used and no additional pruning is justified.
5. Verified byte-for-byte that all three node Lean signatures match their files and
that each `proof_deps` is the union of the proof-step uses. Only `proof`, `proof_deps`
and `proof_origin` changed on the existing node. The new nodes have the required
creation, blueprint, source and Lean records. Read `dag/units/sk-thm-picard-duality.json`:
its `realized` fields do not name this node, and this is a reduction below the unit
level along the inherited relative finite Tor argument. No unit statement or step is
bypassed. Verdict: pass.

Changed in this second reading: added this review record only; no Lean, DAG, or statement changes were necessary.
