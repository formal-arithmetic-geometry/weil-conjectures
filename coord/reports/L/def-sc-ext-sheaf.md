# def-sc-ext-sheaf (unit sk-thm-picard-duality), writer W-ext1748

Files: w-ext1748/dag/nodes/sec-picard-framework/def-sc-ext-sheaf.json (written by w-ext1748/write_item.py from the DAG copy). No new node.

## Correction (E7)
The blueprint defines Ext^i_X(F,G) := R^i Hom_{O_X}(-,G)(F), right derived functors of the contravariant Hom(-,G). Mod(O_X) does not have enough projectives, so this is ill-posed (HUMAN.md 14:36 UTC; lead_note). New statement: Ext^i_X(F,G) := R^i Hom_{O_X}(F,-)(G) = H^i(Hom_{O_X}(F,I^•)) for an injective resolution G -> I^• in Mod(O_X). Also stated: independent of the resolution up to canonical isomorphism; canonically isomorphic to Ext^i_{Mod(O_X)}(F,G) = Hom_{D(O_X)}(F,G[i]) of def-pc-ext (Stacks 06XQ, 06XR (1)); Ext^0 = Hom (06XS (2)); long exact sequences in both variables. The statement includes a parenthetical that names the correction. blueprint.same_as = [def-pc-ext].

## Steps (well-definedness)
1. Injective resolutions exist: lem-weil-pbc-scheme-modules-enough-injectives (Stacks 01DH), lem-weil-pbc-left-exact-injective-resolution-degree-zero (1).
2. Hom(F,-) is additive and left exact (elementary).
3. Independence of the resolution and comparison with def-pc-ext come from lem-weil-pbc-ext-via-injective-resolution (Mathlib leaf). R^0 = Hom comes from lem-weil-pbc-left-exact-injective-resolution-degree-zero (2) (Mathlib leaf).
4. Second-variable long exact sequence: lem-weil-pbc-derived-functor-long-exact, with v = Hom(F,-).
5. First-variable long exact sequence: Hom(-,I^n) is exact on short exact sequences (surjectivity is the definition of injective I^n, def-sp-injective-resolutions), which gives a short exact sequence of complexes. Then apply lem-weil-pbc-complex-ses-homology-long-exact (Mathlib leaf).
proof_origin: document, derived.tex Section 06XP.

Tool uses (unit sk-thm-p1, declared in split_report.tool_uses): lem-weil-pbc-scheme-modules-enough-injectives (split, non-leaf) and lem-weil-pbc-derived-functor-long-exact (split, non-leaf) are used as generic tools. The other three are Mathlib leaves.

The partial file w-ext-partial/lem-sc-ext-abelian-hom-long-exact.json was not used. It is correct (Mathlib leaf: Abelian.Ext.addEquiv₀, covariantSequence_exact, contravariantSequence_exact), but the injective-resolution route does not need it. It would be useful if L prefers to define Ext_X as def-pc-ext on Mod(O_X).

## Mathlib searches (actually run)
- LeanSearch: unavailable (HTTP 500).
- Loogle: extAddEquivCohomologyClass, which is general and already the leaf lem-weil-pbc-ext-via-injective-resolution.
- LeanFinder: no Ext for O_X-modules, only Sheaf.H and the instAbelian instances.
- grep of Mathlib: no sheaf-of-modules Ext.

Verdict: a definition, not a Mathlib leaf.

## Lean (slopmaster2)
AlgebraicGeometry.Scheme.Modules.Ext (WeilConjectures/AlgebraicGeometry/Modules/Ext.lean:51-57, sorry-free) is Abelian.Ext on X.Modules, that is Hom_{D}(F,G[i]). This is the corrected definition in its def-pc-ext form. Its docstring repeats the contravariant blueprint wording, and that docstring should be fixed. It is recorded in lean_candidates. lean_audit was left unchanged (state closed).

## Citing nodes (15)
- Already read Ext in the corrected way, so their use does not change: lem-sc-ext-locally-free and lem-sc-p1-ext-locally-free-naturality. Both already state the correction in their steps, via lem-weil-pbc-ext-via-injective-resolution. lem-sc-ext-locally-free can now drop its "(correcting the contravariant wording ...)" remark.
- Their use changes, though the content holds: lem-sc-ext-sheaf-to-global-spectral-sequence. Its abutment is the Grothendieck composite Γ∘Hom(F,-), which is correct only under the corrected definition.
- They use Ext^1 as Yoneda extension classes, so they need the identification with Hom_D of def-pc-ext. The new statement gives that identification, and they are unaffected once they read it: lem-sc-p1-ext-pushout-postcompose, lem-sc-p1-ext-yoneda-associativity, lem-sc-p1-ext-yoneda-functoriality, lem-sc-p1-ext-yoneda-splicing-associative, lem-sc-p1-pullback-extension-class, lem-sc-p1-boundary-one-extension-class, lem-sc-p1-boundary-extension-composition, lem-sc-p1-boundary-connecting-naturality.
- Their use is wrong in scope:
  - lem-sc-p1-ext-class-naturality says "an abelian category C equipped with Ext groups as in def-sc-ext-sheaf". def-sc-ext-sheaf is only for Mod(O_X), so this node should cite def-pc-ext.
  - lem-sc-p1-ext-pushout-postcompose, lem-sc-p1-ext-yoneda-associativity and lem-sc-p1-ext-yoneda-splicing-associative say "ringed space", but the definition is for a scheme.
- Unaffected: lem-sc-p1-duality-pairing-naturality, lem-sc-p1-ext-coherent-dim-one-vanishing, thm-sc-p1-duality.

## Errors in the brief
The Stacks pointer "cohomology.tex ~10995, section Ext groups" is Section 0BQP "Ext sheaves", which defines the sheaf Ext (def-weil-pbc-sheaf-ext's subject). The global Ext groups are derived.tex Section 06XP (06XQ, 06XR, 06XS).

## Checks
- check_dag on a copy of dag/nodes with this file overlaid: 0 cycles, 0 self-loops. The 25 reach and 11 route warnings are the same as on the unmodified DAG.
- review_split def-sc-ext-sheaf: PASS ("0 new nodes; statement changed"). It was run with SHEAF_DAG pointing to the overlay and with head_version read from the DAG file, because the tool's git show cannot see /tmp paths.

WANTED: none. Unfinished: none. Time: 17:48 to 17:52 UTC.
