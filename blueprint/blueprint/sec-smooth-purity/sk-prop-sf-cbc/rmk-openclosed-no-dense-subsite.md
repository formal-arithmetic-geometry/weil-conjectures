+++
id = "rmk-openclosed-no-dense-subsite"
kind = "remark"
title = "Why the dense-subsite route fails"
order = 1518
+++
It is tempting to prove [prop-openclosed-lowerstar-fully-faithful] by
showing that the base-change functor $\et X\to\et Z$ exhibits $\et Z$ as a
dense subsite, so that pushforward along it is fully faithful for formal
reasons. The functor is indeed cover-dense — that is exactly
[lemma-openclosed-etale-lifts-locally] — but it is neither locally full
nor locally faithful, so the dense-subsite criterion does not apply. The
failure is real and not a matter of bookkeeping: two morphisms $V\to V'$ of
schemes étale over $X$ that agree after base change to $Z$ need only agree
on an open subscheme of $V$ containing the preimage of $Z$, and such an open
subscheme is not in general a covering of $V$. The route taken below
replaces the formal argument by the stalk computation
[lemma-openclosed-stalk-lowerstar], where exactly this open subscheme is
allowed to shrink, because a stalk is a colimit over neighbourhoods.
