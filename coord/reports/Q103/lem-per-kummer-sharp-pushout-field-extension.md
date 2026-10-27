## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-sharp-pushout-field-extension.json`: item, split; statement unchanged, eight proof steps, inherited searches retained and new searches appended.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-kummer-pushout-units.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-divisible-abelian-hom-extension.json`: statement, Mathlib leaf; `AddCommGrpCat.injective_of_divisible` at Mathlib/Algebra/Category/Grp/Injective.lean:54, with the explicit extension clause given by `Module.Baer.extension_property_addMonoidHom` at Mathlib/Algebra/Module/Injective.lean:392, applied to `Module.Baer.of_divisible` at Mathlib/Algebra/Category/Grp/Injective.lean:35.
- `citations.json`: verbatim statement quotes for every proof-step citation.
- `searches.jsonl`: actual msearch.py results, preserved as written by the command.

Attachments: none. I searched the project library for the item id and for Kummer, sharp-monoid, fs-monoid, saturation and pushout terminology. The project has field-theoretic Kummer results, ordinary pushout algebra, and injective abelian-group results, but no finished declaration with this item's hypotheses and conclusion. In particular a Kummer field extension is not a Kummer map of characteristic monoids.

WANTED: a direct published reference for the field-valued extension lemma and the local Kummer integralized-pushout units lemma. ILO supplies the Kummer, localization, sharpening and saturation conventions and the geometric place where they are used, not either algebraic lemma verbatim. The item's proof is expressly agent-written. The new monoid node has statement only; its complete intended argument is retained below for the next worker.

What was wrong or missing: the imported item had no proof. Its group completion may identify distinct pushout elements, so one cannot simply extend the pushout map by freely choosing roots. The proof now controls the zero locus through the localized sharp monoids, checks the character kernel, and extends the character by the divisible-group theorem. No statement correction or STATEMENT-DISPUTED issue was found. No invertibility of the Kummer indices, injectivity on the original group completions, or uniqueness has been added.

Unfinished work: none at this stage's one-level split. The new monoid lemma remains unsplit, as required; it is a genuinely smaller algebraic input without a field, field-valued maps, saturation, or the conclusion of the item.

## Sources and route

I read SETUP.md's three levels, GOAL.md, the chapter `sec-deligne-laumon-a1`, the unit `sk-p-dl-a1-perverse`, and the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`, especially Step 3. The existing ancestry leads through regular-pair purity and the Kummer fs-base changes in ILO X 1.8, printed pp.146--147, diagram (1.a). This delivery supplies their geometric-fibre nonemptiness input via the calling node `lem-per-fs-product-finite-comparison`; it does not change any unit statement or replace its route.

For the item and the new monoid node I read ILO VI 2.1 on printed p.71 and VIII 3.1.1--3.1.2 and 3.1.17 on printed pp.98 and 101. VI 2.1 says injective and positive-multiple cofinal on sharp monoids, with no prime-to-characteristic restriction in the definition. VIII defines localization, sharpening and saturation exactly as used here. These are convention references, and the new argument is not misattributed as a theorem of ILO.

For the new Mathlib leaf I read `literature/stacks-project/more-algebra.tex`, label `lemma-injective-abelian`, mapped by `tags/tags` to Tag 01D7, and its extension proof. It gives extension from a subgroup to any ambient abelian group with a divisible target. I also checked the online Tag 01D7 against the local text. The divisibility condition used here is every positive integer, equivalently every nonzero integer with negatives handled by inversion. I read the full signatures and proofs at Mathlib/Algebra/Module/Injective.lean:392--395 and Algebra/Category/Grp/Injective.lean:35--46. The specialization `(Module.Baer.of_divisible D).extension_property_addMonoidHom i hi χ` gives the leaf in one line, for arbitrary source/ambient universes. Using Additive for a multiplicatively written group changes only notation.

## Intended proof of the new monoid node

This is explanatory material for the unsplit node, not a proof stored in its statement. Let \(\bar A=A/U_A\), etc. Sharpening embeds \(\bar L\) in \(L^{\rm gp}/U_L\) and identifies this quotient with \(\bar L^{\rm gp}\); the existing `lem-trf-fs-face-sharpening`, applied to the unit face, states exactly these facts. The local condition implies \(\bar g^{-1}(0)=\{0\}\). Injectivity of \(\bar f\) implies injectivity of \(\bar f^{\rm gp}\): express an element as a difference and use the embedded sharp monoids.

Modulo \(U=i_B(U_B)+i_C(U_C)\), the group presentation for H becomes
\[
V=(\bar B^{\rm gp}\oplus\bar C^{\rm gp})/
 \{(\bar f^{\rm gp}(a),-\bar g^{\rm gp}(a)):a\in\bar A^{\rm gp}\}.
\]
Indeed killing the two unit subgroups first turns the image of \(A^{\rm gp}\) into the image of \(\bar A^{\rm gp}\), since its quotient map is surjective. The map \(\bar C^{\rm gp}\to V\) is injective: if \((0,c)=(\bar f^{\rm gp}(a),-\bar g^{\rm gp}(a))\), injectivity of \(\bar f^{\rm gp}\) forces \(a=0\), hence \(c=0\).

If \(\bar b\in\bar B,\bar c\in\bar C\) have zero sum in V, choose \(n>0\) and \(\bar a\in\bar A\) with \(n\bar b=\bar f(\bar a)\). Then the image of \(\bar g(\bar a)+n\bar c\) in V is zero, so it is zero in \(\bar C^{\rm gp}\). Both summands lie in the sharp integral monoid \(\bar C\), and a sum is zero there only if both summands are units, hence zero. Locality of g gives \(\bar a=0\), and \(n\bar b=0\) implies \(\bar b=0\): its inverse is \((n-1)\bar b\). The same argument gives \(\bar c=0\). Thus a positive pair from B,C maps into U only when both components are units. In particular the two legs reflect membership in U. Finally if \(x,y\in M\) and \(x+y=0\), represent their sum by a positive pair \((b+b',c+c')\). The preceding result makes both sums units; each of b,b',c,c' is then a unit. Therefore \(x\in U\), proving \(M\cap(-M)\subset U\); the reverse inclusion follows since U is a subgroup contained in M. This proves every clause of the new node without any field or saturation argument.

## Searches and nonduplication

All new-node Mathlib searches were made with the required msearch.py command, and each node's query text is copied from searches.jsonl. No unavailable service is recorded as a negative result. The first character query found Q/Z character constructions and the first Loogle query returned zero hits; the second semantic phrasing found the general Baer extension theorem. The node records the actual hit and exact file lines. The monoid searches returned ordinary `Monoid.PushoutI`, its group-injection results, and `isUnit_map_iff`. I read PushoutI.lean:54--63,192,588--593 and Units/Hom.lean:270--284: the former concerns ordinary, potentially noncommutative pushouts with group assumptions; the latter assumes locality and cannot prove it for this pushout. The focused grep for Kummer|sharp in GroupTheory returned zero hits, while the broader saturation grep found only general subgroup-saturation definitions.

Before creating either node I searched the whole DAG by tag, keywords and expected declarations, and ran blueprint_refs.py searches for sharp, divisible, character group, pushout monoid, Kummer, Kummer pushout and 01D7. I read the candidate statements listed below, not just their filenames. No blueprint statement duplicates either new node. Their blueprint.from ancestor is the one printed by blueprint_refs.py ancestor; the via chain prepends the item, and their exact role is recorded in from.place. The item keeps its original place and has same_as=[] after the full-blueprint search.

## Not duplicates

lem-per-local-kummer-pushout-units vs lem-per-kummer-sharp-pushout-field-extension: the child is solely about units and locality in the integralized pushout of already localized fs monoids; it has no field, compatible field-valued maps or saturation, and does not imply the item without the character-kernel, divisibility and saturated-unit-face arguments.

lem-per-local-kummer-pushout-units vs lem-per-kummer-saturated-pushout-algebra: that existing node assumes a Kummer map on the entire monoids and an invertible annihilator for its scheme-theoretic assertions; it neither covers a map Kummer only after sharp localization nor states the unit-reflection assertion needed here.

lem-per-local-kummer-pushout-units vs lem-per-integral-monoid-unit-pushout: that node pushes a single integral monoid out along a submonoid into a group; it does not treat two local fs legs with a Kummer map on their sharps, and does not give the new unit calculation.

lem-per-local-kummer-pushout-units vs lem-sfb-integral-monoid-unit-pushout: the same distinction applies to this parallel unit-pushout statement in the six-functor-basics unit; neither positive leg here is assumed to be a group.

lem-per-local-kummer-pushout-units vs lem-trf-fs-face-sharpening: that node is about localization/sharpening of one fs monoid and identifies its group quotient; it gives no pushout units. It is reused as the generic tool rather than duplicated.

lem-per-local-kummer-pushout-units vs lem-trf-smooth-toric-saturated-sharp-reduction: the existing statement assumes smoothness of a monoid algebra and yields splitting/regularity for one monoid; it does not concern the present pushout diagram.

lem-per-divisible-abelian-hom-extension vs lem-per-divisible-unit-lattice-extension: the existing node constructs an enlargement of a finite free source lattice under n-divisibility and torsion-free quotient hypotheses; it does not extend an arbitrary prescribed character on a subgroup to its fixed ambient group.

lem-per-divisible-abelian-hom-extension vs lem-sfb-divisible-unit-lattice-extension: the same distinction holds for this parallel lattice-extension statement. There was no existing node with source Tag 01D7 or this Baer extension statement.

## Review by Q103

I checked delivery-errors B--E with all three node files and the source passages open. The item retains every hypothesis: three fs monoids, compatible field-valued maps, algebraically closed target, injective root-cofinal sharp h. The output is one extending homomorphism, with no uniqueness and no invertibility added. The two new statements introduce their objects and quotient constructions, define locality/divisibility inline, cite the fs convention where used, and contain no proof or proof dependency. Their TeX uses single escapes after JSON decoding. The monoid statement is not a renamed clause of the item: the nonzero coefficient character and the saturation extension still have to be built in the item's proof.

Step 1 cites `lem-trf-fs-face-sharpening`, whose statement explicitly gives the localized fs monoid, exact unit subgroup, integral sharp quotient and group-completion quotient. These are precisely what the step takes. Faces and the inverse-image equalities follow from nonzero products in a field. To check locality I wrote out the difference argument, rather than assuming h is local before localization. Both legs are local after localization, even though only the sharp h is Kummer. The other maps and sharp quotients are exactly those of the original statement.

Step 2 cites `def-trf-fs-log-blowup` only for its explicit generators-and-relations definition of group completion. The displayed quotient presentation satisfies that definition: group-valued compatible pairs factor uniquely. This finite presentation argument is elementary. It does not use any nonexistent claim that the ordinary monoid pushout is integral.

Step 3 cites `lem-per-local-kummer-pushout-units`. I compared every hypothesis with Step 1 and the explicit H of Step 2: fs, locality of both legs, and injectivity/root-cofinality of the sharp first leg all hold. The child's statement says both the exact unit subgroup and the two inverse-image equivalences, so this is not borrowing a construction from the child's intended proof.

Step 4 again cites `lem-trf-fs-face-sharpening` for its stated identification of sharp group completions with quotients by face groups. I checked the injective sharp group map by expressing an element as a difference, and checked the sign in the kernel relation: the vector is (f(p),-g(p)), so the product of its character values is a quotient equal to one. Agreement of a and b on P extends to the unit face group by the displayed localization formulas. This proves character descent even when the original map h on groups has a kernel; the only injectivity used is on sharp group completions.

Step 5 cites `def-weil-algebraic-closure` exactly for a root of the nonconstant polynomial X^n-z, and the new divisible-group leaf exactly for extension along the injective inclusion U into H. Nonzeroness of the root follows because z is nonzero. I checked characteristic p with n divisible by p: existence still holds and no separability or unique-root assertion is used. The multiplicative/additive notation switch has no mathematical content.

Step 6 is the elementary root-witness calculation for the unit subgroup of T: use a common positive multiple of x and -x, and then Step 3. It neither assumes T is sharp nor requires a theorem asserting compatibility of saturation with a pushout. Step 7 is the elementary verification that extending a character by zero off the unit face is multiplicative; the two explicit inverse formulas show that the complement of the unit face is an ideal. Step 8 proves preservation of each original support by the identity -b=(n-1)b-nb, uses the already constructed character on units, and restricts along the explicitly proved inclusion S^fs into T. These elementary calculations are written in separate short steps; none hides a comparison or a standard external result. No step exceeds 2000 characters.

For small cases I checked P=Q=R=0; all three monoids groups, including torsion groups; and N to N via multiplication by n with the generator evaluated at zero and at a nonzero value. The all-group case is exactly extension of an existing unit character, and torsion relations are respected because the character is first defined on the image subgroup U. For P=Q=R=N with h multiplication by 2 and k multiplication by 3 and generator values zero, H=(Z+Z)/(2,-3), M is the numerical semigroup generated by 3 and 2, and saturation adds the generator 1 without creating a unit: the extension sends every positive element to zero. If all generator values are nonzero, localization makes all monoids groups and algebraic closedness supplies the required roots. The same checks with p-divisible exponents in characteristic p do not require invertible indices. For the new lemma the degenerate sharp A=B=0 and arbitrary sharp C has H/U=C^gp and units exactly U, while the all-group case has M=H=U. For the new Mathlib leaf V=0, V=W, and finite torsion ambient groups all agree with the extension theorem; no finite-generation assumption is present or needed.

Corrections during review: I separated the final saturation, extension-by-zero, and support/restriction calculations into three elementary steps so their arguments can each be checked directly; the mathematical statement did not change. I retained the existing face-sharpening lemma as a declared generic off-unit tool in split_report.tool_uses, and did not create a duplicate or edit maintainer-owned tool_uses. All cited statements have verbatim copies in citations.json, and the proof_deps list is exactly the union of uses. No node depending on the item is used as a premise. No forbidden SGA source, Lean edit, compiler or local DAG checker was used.

## Dry-run repairs

The first full dry run rejected only metadata on the divisible-group leaf: no definition citation and no structured mathlib_match.line. I opened `def-sp-injective-resolutions` and read its exact injectivity definition (surjectivity of restriction along every monomorphism). The leaf now names that notion and immediately writes its explicit extension meaning, so the citation defines exactly the notion taken from it. Its direct Mathlib match is AddCommGrpCat.injective_of_divisible, file Algebra/Category/Grp/Injective.lean, line 54; I had already read lines 54--57. The explicit homomorphism formulation remains backed by the previously read Baer extension declaration at line 392. I regenerated the verbatim quote for Step 5. No hypothesis, conclusion, route or proof argument changed. I also made the first unsuccessful character queries explicitly have verdict no match instead of sharing the later successful verdict.
