+++
id = "thm-pd-fpqc-local-properties"
kind = "theorem"
title = "Properties of morphisms are local in the fpqc topology on the target"
order = 867
uses = ["def-pc-base-change", "def-pc-finite-locally-free", "def-pc-morphism-conventions"]
+++
Let $k\subseteq K$ be a finite field extension and let $Z$ be a scheme over $k$
such that $Z_K=Z\times_kK$, the base change of
$Z$, is of finite type and smooth over
$K$, proper over $K$, and connected.
Then $Z$ is of finite type and smooth over $k$, proper over $k$, and connected.
The corresponding statements, together with the case of a faithfully flat
morphism that is merely locally of finite presentation, are Stacks Project,
Descent, Section 35.23, Tag
[02YJ](https://stacks.math.columbia.edu/tag/02YJ); for smoothness the
precise statement is Lemma 35.23.29, Tag
[02VL](https://stacks.math.columbia.edu/tag/02VL), for local finite
presentation Lemma 35.14.3, Tag
[02KL](https://stacks.math.columbia.edu/tag/02KL), and for smoothness
along a faithfully flat morphism which is locally of finite presentation
Lemma 35.14.5, Tag
[05B5](https://stacks.math.columbia.edu/tag/05B5).

## Proof

A finite field extension $k\subseteq K$ makes $\Spec(K)\to\Spec(k)$ a
surjective [def-pc-finite-locally-free]
morphism, in particular faithfully flat, quasi-compact, and locally of finite
presentation, so it is an fpqc covering of $\Spec(k)$ in the sense of Stacks
Project, Descent, Section 35.23, Tag
[02YJ](https://stacks.math.columbia.edu/tag/02YJ); the scheme $Z_K$ is the
base change of [def-pc-base-change], and smoothness and properness are the
notions of [def-pc-morphism-conventions].

*Being of finite type and smooth.* The morphism $Z_K\to\Spec(K)$ is
locally of finite presentation, and $Z_K\to Z$ is surjective flat and of finite
presentation, so $Z\to\Spec(k)$ is locally of finite presentation by Lemma
35.14.3, Tag [02KL](https://stacks.math.columbia.edu/tag/02KL); since
$Z_K$ is quasi-compact over $K$ and $Z_K\to Z$ is surjective, $Z$ is
quasi-compact, hence of finite type. Smoothness of $Z\to\Spec(k)$ then follows
from smoothness of $Z_K\to\Spec(K)$ by Lemma 35.14.5, Tag
[05B5](https://stacks.math.columbia.edu/tag/05B5), applied to the
surjective flat locally finitely presented morphism $Z_K\to Z$; this is the
same lemma that Stacks Project, Lemma 39.9.4, Tag
[0BFC](https://stacks.math.columbia.edu/tag/0BFC), invokes for abelian
varieties, there in the form Lemma 35.23.29, Tag
[02VL](https://stacks.math.columbia.edu/tag/02VL).

*Properness.* This is one of the properties of morphisms proved to be
local in the fpqc topology on the target in Stacks Project, Descent, Section
35.23, Tag [02YJ](https://stacks.math.columbia.edu/tag/02YJ):
separatedness and universal closedness are separated in the list of that
section, and properness is their conjunction together with being of finite
type, which was settled above.

*Connectedness.* The morphism $Z_K\to Z$ is the base change of the
surjective morphism $\Spec(K)\to\Spec(k)$, hence surjective. The image of a
connected space under a continuous map is connected, so $Z$ is connected
because $Z_K$ is.
