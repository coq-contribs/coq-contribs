Concerning Jenkins
==================

The `coq-contribs` [view](https://ci.inria.fr/coq/view/coq-contribs/) contains multiple items:
- [coq-contribs-v8.5](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-v8.5) tracks whether all coq-contribs are compilable with Coq 8.5;
- [coq-contribs-v8.6](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-v8.6) tracks whether all coq-contribs are compilable with Coq 8.6;
- [coq-contribs-trunk](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs-trunk) tracks whether all coq-contribs are compilable with Coq trunk;
- [coq-contribs](https://ci.inria.fr/coq/view/coq-contribs/job/coq-contribs) enables one to check whether all coq-contribs are compilable with a given branch of Coq.

How to remove a coq-contrib from Jenkins
========================================

For each of the above jobs
- click the `Configure` link;
- in the form that will appear find `Define build flow using flow DSL`;
- the (huge) edit-box to the right of it defines the behavior of this job (in Groovy programming language --- that's supposed to be a hyppie language for the Java platform™).
- find the line talking about the coq-contrib you want Jenkins to stop tracking; it will look like
```
{build("bench-THE-NAME-OF-THE-COQ-CONTRIB", working_directory: working_directory)},
```
- remove that line
- click the `Save` button.

Since the `bench-THE-NAME-OF-THE-COQ-CONTRIB` job is no longer needed, one can delete it also.
- Select the view that shows [all Jenkins jobs](https://ci.inria.fr/coq/);
- visit the job corresponding to the coq-contrib Jenkins no longer tracks. Its name has the form `bench-THE-NAME-OF-THE-COQ-CONTRIB`;
- click the `Delete project` link.
