## Worker report

Files written under dag/nodes/sec-deligne-laumon-a1/:

- lem-per-kato-lattice-chart-realization.json: item, split in ten steps; no Mathlib match.
- lem-per-log-smooth-infinitesimal-calculus.json: new statement, unsplit, no Mathlib match.
- lem-per-lfp-unique-infinitesimal-lifts-etale.json: new statement, unsplit, no Mathlib match.
- lem-per-integral-chart-logification-thickening.json: new statement, unsplit, no Mathlib match.

Attachments: none. Searches for the exact blueprint tag, Kato/lattice/chart terminology, LogScheme, LogStructure, logification and the new ids in WeilConjectures of slopmaster2 and upstream master found no project theorem giving the item or the new inputs. Upstream sorry declarations are not treated as proofs.

WANTED: Kato (1988), Logarithmic structures of Fontaine--Illusie, section 1 (associated log structures) and section 3 (logarithmic differentials, infinitesimal log smoothness and Theorem 3.5), for lem-per-integral-chart-logification-thickening and lem-per-log-smooth-infinitesimal-calculus. ILO is present and read; it attributes the chart proof to Kato but does not supply the full infinitesimal calculus. The item proof is consequently marked agent-written. No unavailable source is claimed to have been read, and no download was made.

The item statement is unchanged. Its source ILO XVI Proposition 3.6.3, printed p.252, last paragraph, defines exactly P as the inverse image under the extended lattice map and asserts the chart and etale comparison. The parent uniformizer-chart split already corrected the source's preceding finite-cokernel sentence to mean the quotient by units. This item assumes the needed extension explicitly, so no statement correction is needed here.

The interrupted work had saved the item, two new nodes, a script, source text, and logged Mathlib searches, but no report or completed delivery. I retained the proof and those searches, compared its statement with the current repository, and repaired the arbitrary-test-scheme issue before packaging. The old associated-log node is locally Noetherian; using it on arbitrary affine square-zero tests would violate C4/E1. The third node supplies exactly the general construction, integrality, universal property and strict-restriction fibers used there. I also added the existing affine-target representability node at the chart-map and affine-base-change identifications rather than silently taking those identifications from a definition.

Nothing in this stage-1 split is asserted Lean-proved. The three new statements deliberately remain unsplit, with empty proof/proof_deps and null proof_origin; their future proofs are separate DAG items. No Lean file, compiler, Lake tool, live project file or launcher script was written or run.

## Not duplicates

lem-per-log-smooth-infinitesimal-calculus vs lem-per-log-smooth-differential-generators: the existing node chooses a dlog basis at one stalk and controls a characteristic cokernel; it does not give infinitesimal lifts or the derivation torsor. The new calculus has no prescribed lattice and does not conclude existence of an etale toric chart.

lem-per-log-smooth-infinitesimal-calculus vs lem-per-kato-lattice-chart-realization: general infinitesimal log-smooth deformation calculus does not construct P, prove its chart property, or prove the comparison etale. The item's correction argument remains in steps 8--10.

lem-per-integral-chart-logification-thickening vs lem-trf-associated-log-universal-stalks: the existing theorem assumes X locally Noetherian and has no strict square-zero restriction/fiber assertion; the new theorem is on any scheme and is applied to arbitrary infinitesimal test schemes. The existing theorem is insufficient as a black box for those tests.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-weil-pbc-flat-unramified-formally-etale: the existing statement starts from flat and unramified and proves unique lifts, the reverse direction from the new LFP-plus-unique-lifts criterion; flatness and unramifiedness are not hypotheses of the new statement.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: the existing statement starts from etaleness and concludes smoothness and fiber dimension; the new statement deduces etaleness from infinitesimal tests.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-cbc-enhanced-functor-cone-calculus: the shared string 02HM occurs in existing metadata, but that statement concerns quasicategory cone mapping spaces, not schemes or infinitesimal tests.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-coef-local-transport-section-colimits: the existing statement concerns colimits of coherent sections of a locally cocartesian fibration, not scheme etaleness.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-coef-universal-arrow-comparison: the existing statement is uniqueness of an infinity-categorical universal arrow, not the scheme infinitesimal criterion.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-sc-etale-at-prime-formally-etale-cotangent-criterion: the existing statement characterizes ring-local formal etaleness by two cotangent modules; it has no scheme LFP-plus-lifting criterion.

lem-per-lfp-unique-infinitesimal-lifts-etale vs lem-sc-etale-at-prime-flat-unramified-criterion: the existing statement uses formal etaleness at a prime, ordinary flatness and differentials; the new statement directly relates arbitrary affine lifting tests of a scheme morphism to etaleness.

## Review by N4

I read the item, its parent lem-per-trait-log-smooth-uniformizer-chart, the chapter sec-deligne-laumon-a1, unit sk-p-dl-a1-perverse, and the inherited purity/log-alteration ancestry. I read ILO XVI 3.6.1--3.6.4, printed pp.252--253, and VI 1.1, printed p.69, in the saved PDF text. The item realizes the prescribed inverse-image monoid argument in the final paragraph of 3.6.3, not a new route for the perverse proposition. No unit statement or realization field changes.

For the ordinary new criterion I read Stacks more-morphisms.tex definition-formally-etale (02HG), lines 1508--1521, and lemma-etale-formally-etale (02HM), lines 1705 onward, including its affine-local converse proof. Its hypotheses are exactly local finite presentation and unique lifts for affine first-order thickenings; no flatness hypothesis is added. For the two logarithmic inputs I read ILO's actual conventions and invocation of Kato, and clearly labeled the stronger general statements agent-formulated with WANTED primary references. General log-smooth calculus is a strictly smaller deformation input; neither it nor logification asserts the item's prescribed-chart conclusion.

Step 1 uses the definition's chart pushout and the full face-sharpening statement: localization at the face, units equal F^gp, sharp fs quotient embedded in its finite free group. The inverse-image assertion is proved in the step using the copy of A-units in B. No log-regular hypothesis is taken from a definition or from the proof of a cited node.

Step 2 uses the finite-free subgroup theorem, whose statement applies to K after choosing the finite basis of G. Surjectivity G -> C is assumed in the item. The explicit section constructed from lifts of a basis of C proves the direct decomposition; no abstract splitting theorem is hidden. Step 3 writes generators, the saturation argument and the group-generation argument. Step 4 writes both directions of the pushout bijection, including p'=p+k and the unit relation. Those steps use only the preceding results and the recorded fs/chart definitions.

Step 5 uses the spreading theorem's actual prescribed-germ conclusion, after step 4 checks its E=K pushout hypothesis. Finite generation of Q is essential for spreading finitely many equality germs simultaneously; the base chart is never changed. The affine-target bijection constructs the chart scheme morphism from its monoid-ring map; the fibre-product definition then supplies the comparison.

Step 6 uses finite local freeness and etale localization from the new log-smooth calculus. The determinant/adjugate calculation explicitly spreads the given stalk basis. Invertibility of n is also spread before testing thickenings. Step 7 uses underlying LFP from that same statement and finite monoid presentation from lem-trf-fg-commutative-monoid-finite-presentation. The affine formula is justified by affine-target representability plus the fibre-product universal property, and the displayed D-algebra presentation proves the comparison LFP. It does not infer comparison LFP merely from W/Y being LFP.

Step 8 originally used a locally-Noetherian logification lemma outside its hypotheses; I corrected that citation. The new arbitrary-scheme theorem now supplies fine integral test log structures, the universal log map, and the exact fibers under 1+I. The log-smooth calculus applies because the thickening is strict and square zero and f is chart-log-smooth. The error homomorphism is constructed in the step from unique fiber ratios, and is zero on Q because the two maps are over Y.

Step 9 uses the calculus's explicit action of a derivation and the given differential basis to kill the error on Z^r. The group quotient hypothesis then kills it on all of G: n is a unit on T, so n^k epsilon(g)=0 implies epsilon(g)=0. This is the substance of etaleness and remains in the item, not in a restated child. Affine-target representability and the fibre-product property justify that matching chart and base maps match the comparison.

Step 10 uses the logification universal property for every pair of ordinary lifts and the derivation torsor to prove uniqueness, since a derivation zero on a basis is zero. The representable-presheaf sheaf theorem applies to the arbitrary T-scheme T x_Z W, so the locally existing lifts glue, including on non-affine overlaps. The new 02HM criterion then applies with the LFP property from step 7 and the proved global unique affine-test lifts. Each cited statement was opened; citations.json contains verbatim statement text for each step/node pair.

Small cases checked: P=0 and G=0; r=0 and the empty differential basis; n=1; nontrivial kernel K giving invertible chart generators; trivial log structures on smooth affine space with invertible coordinate 1+x near x=0; and a Kummer chart N -> N, 1 -> d, with d invertible. In the latter the test-unit error is killed by multiplication by d, which explains the invertibility requirement. Without it, in characteristic p, the nonzero unit 1+epsilon has pth power 1 in k[epsilon]/epsilon^2, so unique lifting would fail. For the new logification statement I tested P=N at a zero-valued chart, P=Z with unit-valued chart, P=0, and non-Noetherian test rings: unit lifting is 1+I and integrality makes its action free. For the new ordinary criterion open immersions and identities pass; A^1 -> Spec k has multiple dual-number lifts and is correctly excluded. The log-smooth calculus recovers ordinary smooth derivations for trivial log structures and the expected zero relative derivations for an invertible Kummer chart.

I searched all DAG statements for the notions and all metadata for 02HG/02HM; searched the whole blueprint with blueprint_refs.py for infinitesimal, associated log, formally etale, logarithmic, log smooth, and the Kato/lattice wording; and searched both named project source trees. The only blueprint hits for logarithmic are unrelated zeta/trace terminology. The nearby associated-log, face-sharpening, subgroup, finite-presentation and spreading nodes were read and reused where their hypotheses suffice. The Mathlib searches were retained from searches.jsonl, with new logification searches added using msearch.py only. Ring-level Etale and square-zero derivation declarations, ordinary scheme Etale, and ordinary Kahler-differential local freeness were inspected; none gives the logarithmic statements or the scheme infinitesimal criterion in one specialization. No new Mathlib leaf is claimed.

B--E self-check: all three new nodes are self-contained statement-only nodes with notions cited or defined inline, valid TeX, precise source places and candid WANTED references, own created/blueprint/lean_audit fields, and logged search records. None is elementary, a duplicate, or a clause merely renamed. Cited theorem hypotheses are checked above, no statement is borrowed from the proof of a node, and the proof-dependency union is exact. There is no SGA source or route change. The four generic off-unit tools are declared in split_report.tool_uses for maintainer review. Each proof step is under 2000 characters, so no long step hides an extra lemma.
