# Stage-1 report: lem-trf-open-extension-adjoint

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-open-extension-adjoint.json`: statement, split; not a Mathlib leaf. Five explicit proof steps, six existing dependencies, no new nodes.
- `citations.json`: twelve step/dependency quotes copied verbatim from the six cited statements.
- `searches.jsonl`: the five real searches performed with msearch.py; their results were read and recorded in the item. All inherited searches remain intact.

## Attachments

None. I searched the specified slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, item id, extension-by-zero and exceptional-adjoint terminology, and read `SixFunctors/ProEtale/TraceFormula/Localization.lean` (especially its introduction and openPieceCoeff at line 185) and the related operation definitions. Its openPieceCoeff defines a Frobenius graph coefficient, not this assertion for arbitrary f,t,h,z,u. The introduction explicitly says that open-counit compatibility needs a comparison not supplied by that package. Its trace additivity theorem ends in sorry. No full project declaration asserting both clauses was found. The read-only upstream master is not treated as a finished proof.

## WANTED

None. All sources used are available locally.

## Audit findings and changes

The item already has a correct self-contained statement and precise blueprint ancestry from the reviewed Q74 split. I kept its statement, statement dependencies, source, created record, chapter, unit and inherited Mathlib searches unchanged. There was no prior sandbox item, proof, report or searches log to recover. The only substantive missing field was its proof.

The whole blueprint searches for “open extension”, “extension by zero”, “counit open” and “Exceptional adjoint”, and concept searches of all DAG files, found the needed existing tool `lem-trf-open-square-exchange`. In particular, its statement includes the restriction-identity normalization which the more general `lem-cbc-proetale-extension-zero-base-change` statement does not spell out. I reused the former rather than adding an open counit/base-change lemma. `def-weil-pbc-composite-adjunction` and `def-weil-pbc-adjunction-conjugate` already supply the categorical formulas and are Mathlib leaves. No new node merely restates a clause of the item.

I did not cite `fix-prop-adjunctions` for unconditional existence: its exceptional clause has the stronger ambient admissibility hypothesis, whereas this item uses the specified constructible adjunction datum of `def-trf-admissibility`. That datum explicitly specifies the natural units/counits, triangle identities and conjugate composition comparisons assumed here. The existence of the ordinary open adjunction and the invertible open unit is instead taken from the theorem `prop-weil-open-closed-recollement-adjunctions`, not inferred from a definition. Complementary closed subschemes may be chosen for both opens in these Noetherian finite-type schemes; the calculation only uses the open part of that theorem.

The item is not itself a one-line Mathlib specialization. The logged searches return ordinary scheme-module restriction adjunctions, topological compact-support extension, generic adjunction hom equivalences and global-section naturality. Their returned signatures do not contain the specified exceptional compact-support comparison or the additional open-counit equation. I read the relevant Mathlib source formulas for Adjunction.homEquiv and its naturality (Basic.lean, lines 162–182 and 226–246) and conjugation (Mates.lean). These justify retaining the existing generic Mathlib leaves, not marking the geometric item as a new leaf. A second semantic phrasing was tried before concluding no match. No service was unavailable in these five searches.

## Unfinished work

None for this split. There are no new unsplit children and no Lean changes or builds. Server checks and direct delivery are performed with deliver.py.

## Not duplicates

No new nodes. The existing open-square exchange is a general source-comparison theorem with an explicit restriction normalization; the current item computes the exceptional transpose of an extended coefficient and its compatibility with the open counit. Neither that tool nor the exceptional-tensor/open-Hom comparisons states this whole item. The existing composite-adjunction and conjugation definitions are reused as tools rather than duplicated.

## Review by Q56

I read the chapter record `sec-trace-formula`, the unit record `sk-i-additivity`, and both current blueprint files for `lem-trf-trace-triangle-compatibility` in main-20261015. This item serves exactly the induced-morphisms paragraph of that unit's trace-triangle proof, not its filtered trace-additivity argument. It is not the unit's key node, so no unit record was edited. I read Varshavsky, “Lefschetz–Verdier trace formula and a generalization of a theorem of Fujiwara”, §§1.1.6(a)(i), 1.1.8(ii), 1.1.9, 1.5.9, and 5.3.3 in the local PDF. His source leg is our t and his target leg is our f. The compact-support pushforward formula in §1.1.6 gives the first assertion. The pullback construction in §1.1.8 and the open graded-piece characterization at the end of §5.3.3 give the second assertion after transposing. Since the intermediate adjunction calculations are supplied explicitly here rather than copied from a source proof, proof_origin.by is agent. No forbidden SGA source is used.

For step 1 I read the full statements of `lem-trf-open-square-exchange`, `prop-functor-package` and `def-trf-admissibility`. The first gives precisely b_L and says that its restriction is the identity. The package gives the compact-support composition with natural coherent comparisons, precisely C_N: F e_!N → j_!H N. I checked that the Cartesian square used here is the t-square: V=t^{-1}(U). The coefficient ring is finite and every scheme and morphism is in the separated finite-type k setting. All constructible finite-Tor domains are the ones specified by the item's operation datum; no ambient pro-etale adjoint is assumed.

For step 2 the cited admissibility datum supplies exactly the exceptional adjunction, with natural counit and triangle identities. I wrote the transpose as ε_f F(z_X), substituted the defining transpose of d_L, and used naturality of C to move e_!z across C. This yields j_!(ε_h H(z)) after precisely C F(b_L), proving the first clause without treating its conclusion as an external lemma. This is a short elementary calculation from the stipulated adjunction and step 1.

For step 3 I read `prop-weil-open-closed-recollement-adjunctions`, `def-weil-pbc-composite-adjunction`, and `def-weil-pbc-adjunction-conjugate` in full, and checked the conjugate normalization in `def-trf-admissibility`. The open theorem gives E ⊣ e^* and J ⊣ j^* with invertible units. The composite definition gives the displayed Hom bijections and the counits ε_f F(c_e) and c_j J(ε_h). The conjugation definition gives the unit–transformation–counit formula and invertibility of the conjugate of an isomorphism. Applying it to the inverse of C has the required direction χ:e^*f^!K → h^!j^*K. Expanding this formula and cancelling the adjacent unit/counit proves (*). This calculation is displayed, not assumed as an uncited exceptional base-change theorem. In particular the square fe=jh need not be Cartesian, and the proof does not apply the Cartesian open-base-change theorem for f to it.

For step 4 I checked the precise normalization clause of `lem-trf-open-square-exchange` and the open unit of `prop-weil-open-closed-recollement-adjunctions`. Under N=e^*t^*K=r^*j^*K, the two maps E N→t^*K transpose to the same identity. On the left this is exactly r^* of the triangle identity j^*c_j composed with η_j. This verifies (**) for the actual canonical base-change map, rather than for some unnamed isomorphism between the same objects.

For step 5 I used only the stipulated exceptional counit and the open counit's naturality, as stated by the two cited nodes. The typed chain starts at F E N. Its second equality is naturality of c_e at u:Q→f^!K; the third uses (*); the fourth uses naturality of C at e^*u and the definition z=χ e^*u. Cancelling F(b_L^{-1}) by composing with F(b_L) gives exactly the requested equation on F t^*j_!j^*K. I checked the direction and object of every C, b and counit in this chain. All twelve citations have verbatim statement quotes in citations.json. Statements of dependencies, not their proofs or docstring constructions, are the interfaces used.

I tested the argument with U=X (b and the open counits become identities, so the result is ordinary exceptional transposition), U empty or V empty (the sources and both composites vanish), L=0, K=0, and z=0 or u=0. I also checked a nonempty non-Cartesian f-square: take X equal to the affine line over k, U=P equal to the complement of 0, f the inclusion and t(x)=x−1. Then V is P minus {1}, whereas f^{-1}(U)=P; the map h is the inclusion of V into U. All hypotheses hold and V is strictly smaller than f^{-1}(U). The proof still uses only composition, and nowhere requires V=f^{-1}(U). No invertibility assumption on either coefficient morphism was introduced. Every proof step is below 2000 characters (700, 703, 1324, 694, 904); there is no long standard comparison or separate subclaim hidden in a long step. The generic adjunction formulas are existing Mathlib nodes, and no new lemma is needed for the two-line naturality calculations. The statement and all its edge cases remain unchanged.
