#!/usr/bin/perl -w
#
# TODO
#  * document bin1_is/l1 parameter
#  * make parameters consistent: -leo_bin/l and -leo_bin2/l2 with bin1_is/l1
#  * document support of variables (eg. %S) for post_run parameter

=head1 NAME

leo_diff - comparing runs of Leo-II

=head1 SYNOPSIS

B<leo_diff> -c_t <timeout> -l <path to Leo-II> -p1 <param list 1> -p2 <param list 2> PROBLEMS

B<leo_diff> -T <path to TreeLimitedRun> -c_t <timeout> -w_t <timeout> -l <path to Leo-II> -p1 <param list 1> -p2 <param list 2> PROBLEMS

PROBLEMS consist of paths to THF-encoded logical problems.

=head1 DESCRIPTION

Compare different runs of Leo-II (using different binaries/parameters) on a batch of problems.

=head1 DEPENDENCIES

TreeLimitedRun by Geoff Sutcliffe may be used as a timeout harness.

=head1 OPTIONS

=over 4

=item B<--cpu_timeout, -c_t> INT

CPU timeout given to TreeLimitedRun, or to Leo-II if TreeLimitedRun isn't used.

=item B<--leo_bin, -l> PATH_TO_FILE

Path to Leo-II binary.

=item B<--leo_bin2, -l2> PATH_TO_FILE

Path to another Leo-II binary. This is used for comparing different builds of Leo-II.
To compare two runs of the same build (but with different parameters) just use B<-p2>;
if no B<-l2> binary is specified then that specified as B<-l1> is used for both runs.

=item B<--paramlist1, -p1> STRING

Parameters given to Leo-II.

=item B<--paramlist2, -p2> STRING

Parameters given to Leo-II during the second run. If an B<-l2> binary is specified I<and>
a B<-p2> value, then the two runs of Leo-II will differ in both the binary used and its parameter values.

=item B<--proportional_comparison_time, -pct> FLOAT

Proportional comparison of timing. This applies only for comparing CPU and wallclock durations of the Leo-II run, used to compute the summary (see L<OUTPUT> below).
Since measurements of such values can vary across runs, it is not sensible to compare them directly. Instead, we alter the comparison as follows: Instead of "X > Y" we use the relation "X >~ Y" defined as "X > Y + (pct * X)". If not "X <~ Y" and not "Y <~ X" then we conclude that "X =~ Y".

=item B<--probs> PATH_TO_FILE

Instead of problems given at the command line, they are read from FILENAME.

=item B<-e>

Any output to STDERR by the child process is captured by the script (rather than ignoring it) and relayed on its STDERR channel. Unfortunately this option cannot be used together with B<-T>, since the standard version of TreeLimitedRun sends STDERR of the child process into STDOUT.

=item B<--TreeLimitedRun, -T> PATH_TO_FILE

Path to TreeLimitedRun binary.

=item B<--wc_timeout, -w_t> INT

Wallclock timeout given to TreeLimitedRun.

=item B<--tptp> STRING

This tells leo_diff that the problem files being used are TPTP problems (and contain an appropriate header). This will then activate additional checks according to the value of STRING, which may be one of the following:

=over 2

=item B<check>

If (during one of the two runs) the prover declares to be Theorem any problems not marked as Theorem in the TPTP header, then a B<!> mark is made in the Summary field of the results.

=item B<norm>

If (during one of the two runs) the SZS status emitted by the prover doesn't match exactly the status given in the TPTP problem, then a B<!> mark is made in the Summary field of the results.

=back

=item B<--verbose, -v> [INT]

Verbose output, where INT=1..2

=item B<--header> INT

Prints out the column names every INT rows.

=item B<--post_run> STRING

Executes STRING in the shell after each call to the prover. This can be used for any clean-up missed by the prover.

=item B<--help, -h>

Shows this page.

=back

=head1 EXAMPLES

The following example tests the effect of the B<-rl> switch on three problems from the TPTP problem set:
  ../tools/leo_diff.pl -l ../bin/leo -T ../bin/TreeLimitedRun \
                       -wc_t 3 -cpu_t 3 -pct 0.2 -p2=-rl \
                       ~/TPTP-v5.4.0/Problems/LCL/{LCL579^1.p,LCL579^1.p,LCL714^1.p}

=head1 OUTPUT

Output consists of a list of rows (one per problem). Using TreeLimitedRun results in richer output, since it provides the CPU- and elapsed-timed duration for the Leo-II process and its children. Each row shows the results for the two runs (one the same problem) side-by-side. The rows are headed by a description row, as in the example below:

        Problem || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || Summary
     LCL579^1.p || 1 | THM |     0 |    3 |   519 |  0.38 |  0.45 || 1 | THM |     0 |    3 |    24 |  0.05 |  0.08 || ----^^^
     LCL579^1.p || 1 | THM |     0 |    3 |   519 |  0.38 |  0.40 || 1 | THM |     0 |    3 |    24 |  0.06 |  0.07 || ----^^^
     LCL714^1.p || 1 | THM |     0 |    3 |    45 |  0.17 |  0.24 || 1 | THM |     0 |    3 |    36 |  0.10 |  0.13 || ----^^^

When TreeLimitedRun isn't used, the output would look like this:

        Problem || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || Summary
     LCL579^1.p || - | THM |     0 |    3 |   519 |     - |     - || - | THM |     0 |    3 |    24 |     - |     - || ?---^??
     LCL579^1.p || - | THM |     0 |    3 |   519 |     - |     - || - | THM |     0 |    3 |    24 |     - |     - || ?---^??
     LCL714^1.p || - | THM |     0 |    3 |    45 |     - |     - || - | THM |     0 |    3 |    36 |     - |     - || ?---^??

=head2 Legend

Some of the fields are self-explanatory. The rest are explained below:

=over 6

=item B<T> : Whether TreeLimitedRun ran successfully (i.e. if T=0 then it indicates that there were problems outside of Leo-II).

=item B<SZS> : SZS status returned by Leo-II. A status of "(U)" means that a status could not be detected.

=item B<LpCnt> : number of iterations of Leo-II's main loop.

=item B<PCnt> : number of calls to external ATPs.

=item B<ClCnt> : clause count at the end of the run.

=item B<Summary> : compares the second run with the first. The values in the row are compared point-wise, and a summary is produced using the following symbols:

=over 2

=item B<-> means that the two results are identical (or "roughly equivalent" if a B<-pct>-liked parameter was used).

=item B<^> means that the second run performed better than the first.

=item B<v> means that the second run didn't perform as well as the first.

=item B<?> means that it is unclear how to compare the two values.

=item B<!> means that the associated value is unusual for one/both problem runs. For instance, this occurs when a problem marked as CounterSatisfiable is claimed to be a Theorem; this would require setting the B<--tptp check> flag. Under B<--tptp norm>, this means that both provers/configurations returned suspicious SZS statuses.

=item B<1> under B<--tptp norm> means that the first prover/configuration returned a suspicious SZS status.

=item B<2> under B<--tptp norm> means that the second prover/configuration returned a suspicious SZS status.

=back

=back

Columns (and positions in the Summary) are ordered in a way such that if a particular parameter is better/worse in one of the runs, then all parameters to its right will probably reflect this too. For instance, in the above example note how the smaller clause count led to shorter durations. For another example, we could compare the performance of the E theorem-prover with Leo-II's "dummy" prover: we could use the same command in the previous example, but use C<-p1 "-f e" -p2 "-f dummy">. This should yields results similar to the following:

        Problem || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || T | SZS | LpCnt | PCnt | ClCnt | CPU t |  WC t || Summary
     LCL579^1.p || 1 | THM |     0 |    3 |   519 |  0.37 |  0.40 || 1 | THM |     7 |    4 |   531 |  0.34 |  0.37 || --vvv--
     LCL579^1.p || 1 | THM |     0 |    3 |   519 |  0.37 |  0.40 || 1 | THM |     7 |    4 |   531 |  0.35 |  0.37 || --vvv--
     LCL714^1.p || 1 | THM |     0 |    3 |    45 |  0.17 |  0.19 || 1 | THM |    12 |    5 |   138 |  0.34 |  0.36 || --vvvvv

=head1 AUTHOR

Nik Sultana

=head1 BUGS

Please write to nik.sultana@cl.cam.ac.uk

=cut

use strict;
use warnings;
use Getopt::Long;
use Pod::Usage;
use File::Basename;
use IO::CaptureOutput qw/capture_exec/;

my %opts = ();
GetOptions("TreeLimitedRun|T=s" => \$opts{TreeLimitedRun},
           "wc_timeout|w_t=i" => \$opts{WC_Timeout},
           "cpu_timeout|c_t=i" => \$opts{CPU_Timeout},
           "leo_bin|l=s" => \$opts{LEO_binary},
           "bin1_is|l1=s" => \$opts{binary1_is}, #FIXME LEO_binary/l/leo_bin are therefore misleading
           "leo_bin2|l2=s" => \$opts{LEO_binary2},
           "paramlist1|p1=s" => \$opts{Paramlist1},
           "paramlist2|p2=s" => \$opts{Paramlist2},
           "probs=s" => \$opts{Probs},
           "verbose|v:i" => \$opts{Verbose},
           "e" => \$opts{ErrorFloat},
           "proportional_comparison_time|pct=f" => \$opts{Proportional_Comparison_Time},
           "tptp=s" => \$opts{TPTP_Problem},
           "header=i" => \$opts{HeaderInterval},
           "post_run=s" => \$opts{PostRun},
           "help|h" => \$opts{help})
    || pod2usage();
pod2usage(-verbose => 2) if $opts{help};

if (not (defined $opts{Verbose}))
{
    $opts{Verbose} = 0;
}
else
{
    $opts{Verbose}++;
}

if (defined $opts{TreeLimitedRun})
{
    if ((not defined $opts{WC_Timeout}) ||
        (not defined $opts{CPU_Timeout}))
    {
        print STDERR "$0: Incomplete timeout parameters: need both WC and CPU timeouts for TreeLimitedRun\n";
        exit 1;
    }
}
else
{
    if (defined $opts{WC_Timeout})
    {
        print STDERR "$0: WARNING: wallclock timeout is irrelevant if TreeLimitedRun isn't used\n";
    }

    if (not defined $opts{CPU_Timeout})
    {
        print STDERR "$0: CPU timeout is required since TreeLimitedRun isn't used\n";
        exit 1;
    }
}

if (not defined $opts{Proportional_Comparison_Time})
{
    $opts{Proportional_Comparison_Time} = 0;
}

if (not defined $opts{LEO_binary})
{
    print STDERR "$0: Paths to Leo-II binary not specified\n";
    exit 1;
}

$opts{Paramlist1} = "" if not defined $opts{Paramlist1};
$opts{Paramlist2} = "" if not defined $opts{Paramlist2};

$opts{HeaderInterval} = 0 if not defined $opts{HeaderInterval};

if (not defined $opts{LEO_binary2})
{
    if ($opts{Paramlist1} eq $opts{Paramlist2})
    {
        print STDERR "$0: No 2nd binary, or different parameters, specified\n";
        exit 1;
    }
    else
    {
        $opts{LEO_binary2} = $opts{LEO_binary};
    }
}
else
{
    if ($opts{LEO_binary2} eq $opts{LEO_binary})
    {
        print STDERR "$0: WARNING: paths to LeoII binaries are identical\n";
    }
}

if ( !(defined $opts{TPTP_Problem}))
{
    $opts{TPTP_Problem} = "";
}
else
{
    if (($opts{TPTP_Problem} ne "check") &&
        ($opts{TPTP_Problem} ne "norm"))
    {
        print STDERR "$0: ERROR: unknown TPTP parameter: $opts{TPTP_Problem}\n";
    }
}

my $leo2K = "leo2";
my $satallaxK = "satallax";
my $agsyholK = "agsyHOL";
if ( !(defined $opts{binary1_is}))
{
  $opts{binary1_is} = "leo2";
}
else
{
  if (($opts{binary1_is} ne $leo2K) &&
      ($opts{binary1_is} ne $satallaxK) &&
      ($opts{binary1_is} ne $agsyholK))
  {
    die "Unrecognised prover: " . $opts{binary1_is};
  }
}

my @problist;
if (not defined $opts{Probs})
{
    @problist = @ARGV;
}
else
{
    open FILE, $opts{Probs} or die ("Could not open problems file (" . $opts{Probs} . ")");
    @problist = <FILE>;
    close FILE;
    chomp(@problist);
}

print "Probs=" . scalar(@problist) . "\n" if $opts{Verbose} > 0;

# SZS statuses. This list is incomplete, but contains the
# union of statuses of all TPTP problems, and the statuses
# returned by Leo-II.
my %szs_statuses =
    ("Theorem", "THM",
     "Unsatisfiable", "UNS",
     "Timeout", "TMO",
     "ResourceOut", "RSO",
     "GaveUp", "GUP",
     "CounterSatisfiable", "CSA",
     "User", "USR",
     "Force", "FOR",
     "Unknown", "UNK",
     "Open", "OPN",
     "Satisfiable", "SAT",
     "Tautology", "TAU",
     "Error", "ERR");

sub run
{
    my $binary = $_[0];
    my $params = $_[1];
    my $prob = $_[2];
    my $prover = $_[3];

    my $cmd;
    if (defined $opts{TreeLimitedRun})
    {
        $cmd = "$opts{TreeLimitedRun} $opts{CPU_Timeout} $opts{WC_Timeout} $binary $params $prob";
    }
    else
    {
        $cmd = "$binary -t $opts{CPU_Timeout} $params $prob";
    }

    print $cmd . "\n" if $opts{Verbose} > 0;

    my ($stdout, $stderr);
    ($stdout, $stderr) = capture_exec (split (/,/, $cmd));

    print $stdout if $opts{Verbose} > 1;
    print $stderr if $opts{ErrorFloat};

    my $UNKNOWN_STATUS = "(U)";
    my $status = $UNKNOWN_STATUS;
    my $clause_count = -1;
    my $loop_count = -1;
    my $foatp_calls = -1;
    if ($prover eq $leo2K)
    {
      if ($stdout =~ m/.+status (.+) for.+clause_count:(\d+),loop_count:(\d+),foatp_calls:(\d+)/)
      {
          $status = $szs_statuses{$1};
          $clause_count = $2;
          $loop_count = $3;
          $foatp_calls = $4;
          print "(Full experiment data obtained)\n" if $opts{Verbose} > 0;
      }
      elsif ($stdout =~ m/.+status (.+) for .+/)
      {
          $status = $szs_statuses{$1};
          print "(Partial experiment data obtained)\n" if $opts{Verbose} > 0;
      }
      else
      {
          print "(No experiment data obtained)\n" if $opts{Verbose} > 0;
      }
    }
    elsif ($prover eq $satallaxK)
    {
      if ($stdout =~ m/% SZS status (.+)/)
      {
          $status = $szs_statuses{$1};
          #Satallax also tells us the mode used
          print "(Full experiment data obtained)\n" if $opts{Verbose} > 0;
      }
      else
      {
          print "(No experiment data obtained)\n" if $opts{Verbose} > 0;
      }
    }
    elsif ($prover eq $agsyholK)
    {
      if ($stdout =~ m/% SZS status ([^ ]+)/)
      {
          $status = $szs_statuses{$1};
          print "(Full experiment data obtained)\n" if $opts{Verbose} > 0;
      }
      else
      {
          print "(No experiment data obtained)\n" if $opts{Verbose} > 0;
      }
    }
    else
    {
      die "Unrecognised prover: " . $prover;
    }

    my $outcome;
    my $cpu_time_taken = 0.0;
    my $wc_time_taken = 0.0;
    if (defined $opts{TreeLimitedRun})
    {
        if ($stdout =~ m/FINAL WATCH: (.+) CPU (.+) WC/)
        {
            $cpu_time_taken = $1;
            $wc_time_taken = $2;
            $outcome = 1; #we've been able to get info from TreeLimitedRun
        }
        else
        {
            $outcome = 0; #a serious error has occurred
        }
    }
    else
    {
        #TreeLimitedRun hasn't been used
        $cpu_time_taken = '-';
        $wc_time_taken = '-';
        $outcome = '-';
    }

    #If prover declares a problem to be a Theorem, but the TPTP header doesn't,
    #then flag this as suspicious.
    my $suspicious_status = 0;
    if ($opts{TPTP_Problem} ne "")
    {
        my $tptp_status_line = `grep -E '^% Status' $prob`;
        my $tptp_status;
        if ( !($tptp_status_line =~ m/^% Status\ +: (.+)$/))
        {
            print STDERR "$0: WARNING: $prob does not appear to be a TPTP problem: no status information found\n";
        }
        else
        {
            $tptp_status = $szs_statuses{$1};
            print "TPTP problem status: $tptp_status\n" if $opts{Verbose} > 0;

            if ($opts{TPTP_Problem} eq "check")
            {
                if (($status eq "Theorem") && ($status ne $tptp_status))
                {
                    $suspicious_status = 1;
                    print "Disagreement: prover ($status) vs TPTP ($tptp_status)\n" if $opts{Verbose} > 0;
                }

            }
            elsif ($opts{TPTP_Problem} eq "norm")
            {
                if ($status ne $tptp_status)
                {
                    $suspicious_status = 1;
                    print "Disagreement: prover ($status) vs TPTP ($tptp_status)\n" if $opts{Verbose} > 0;
                }
            }
        }
    }

    return ($outcome, $cpu_time_taken, $wc_time_taken, $status, $clause_count, $loop_count, $foatp_calls, $suspicious_status);
}

#Header for experiment data
my @result_header = ("T", "SZS", "LpCnt", "PCnt", "ClCnt", "CPU t", "WC t");
#Formatting for the results from a single experiment
my $result_template = '%1$1s | %2$3s | %3$5s | %4$4s | %5$5s | %6$6s | %7$6s';

sub print_result
{
    my @data = @_;
    return sprintf ($result_template, @data);
}

#Print header -- consists of problame name, the experiment data of both runs, and summary
sub columns_header
{
    return sprintf '%1$19s || ' .
        print_result(@result_header) . " || " .
        print_result(@result_header) . ' || %2$2s' . "\n",
        "Problem",
        "Summary";
}

sub postproblemrun_hook
{
    if (defined $opts{PostRun})
    {
        my $prob = basename($_[0]);
        my $postrun = $opts{PostRun};
        $postrun =~ s/%S/$prob/g;
        print "Running postrun: " . $postrun . "\n" if $opts{Verbose} > 0;
        `$postrun`;
    }
}

my $row_no = -1;

if ($opts{HeaderInterval} == 0)
{
    print columns_header();
}

foreach my $prob (@problist)
{
    $row_no++;

    if (($opts{HeaderInterval} > 0) && ($row_no % $opts{HeaderInterval} == 0))
    {
        print "\n" if $row_no > 0;
        print columns_header();
    }

    print "Tackling " . $prob . "\n" if $opts{Verbose} > 0;

    my ($outcome1, $cpu_time_taken1, $wc_time_taken1, $status1,
        $clause_count1, $loop_count1, $foatp_calls1, $suspicious_status1) =
            run($opts{LEO_binary}, $opts{Paramlist1}, $prob, $opts{binary1_is});
    postproblemrun_hook($prob);

    my ($outcome2, $cpu_time_taken2, $wc_time_taken2, $status2,
        $clause_count2, $loop_count2, $foatp_calls2, $suspicious_status2) =
            run($opts{LEO_binary2}, $opts{Paramlist2}, $prob, $leo2K);
    postproblemrun_hook($prob);

    my $marker = "";

    if (defined $opts{TreeLimitedRun})
    {
        if ($outcome1 == $outcome2)
        {
            $marker .= "-";
        }
        elsif ($outcome1 < $outcome2)
        {
            $marker .= "^";
        }
        elsif ($outcome1 > $outcome2)
        {
            $marker .= "v";
        }
    }
    else
    {
            $marker .= "?";
    }

    if (($suspicious_status1 == 1) && ($suspicious_status2 == 1))
    {
        $marker .= "!";
    }
    elsif ($suspicious_status1 == 1)
    {
        $marker .= "1";
    }
    elsif ($suspicious_status2 == 1)
    {
        $marker .= "2";
    }
    else
    {
        #FIXME assumes "Theorem" is the desired result
        if ($status1 eq $status2)
        {
            $marker .= "-";
        }
        elsif (($status1 ne "THM") && ($status2 eq "THM"))
        {
            $marker .= "^";
        }
        elsif (($status1 eq "THM") && ($status2 ne "THM"))
        {
            $marker .= "v";
        }
    }

    if ($loop_count1 == $loop_count2)
    {
        $marker .= "-";
    }
    elsif (($loop_count1 > $loop_count2) && ($loop_count2 > -1))
    {
        $marker .= "^";
    }
    elsif (($loop_count1 < $loop_count2) && ($loop_count1 > -1))
    {
        $marker .= "v";
    }
    else
    {
        $marker .= "?";
    }

    if ($foatp_calls1 == $foatp_calls2)
    {
        $marker .= "-";
    }
    elsif (($foatp_calls1 > $foatp_calls2) && ($foatp_calls2 > -1))
    {
        $marker .= "^";
    }
    elsif (($foatp_calls1 < $foatp_calls2) && ($foatp_calls1 > -1))
    {
        $marker .= "v";
    }
    else
    {
        $marker .= "?";
    }

    if ($clause_count1 == $clause_count2)
    {
        $marker .= "-";
    }
    elsif (($clause_count1 > $clause_count2) && ($clause_count2 > -1))
    {
        $marker .= "^";
    }
    elsif (($clause_count1 < $clause_count2) && ($clause_count1 > -1))
    {
        $marker .= "v";
    }
    else
    {
        $marker .= "?";
    }

    if (defined $opts{TreeLimitedRun})
    {
        #Include threshold for these, to avoid false impressions due to jitter
        if ($cpu_time_taken1 > ($cpu_time_taken2 +
                                ($opts{Proportional_Comparison_Time} * $cpu_time_taken1)))
        {
            $marker .= "^";
        }
        elsif ($cpu_time_taken2 > ($cpu_time_taken1 +
                                   ($opts{Proportional_Comparison_Time} * $cpu_time_taken2)))
        {
            $marker .= "v";
        }
        else
        {
            $marker .= "-";
        }
    }
    else
    {
            $marker .= "?";
    }

    if (defined $opts{TreeLimitedRun})
    {
        #Include threshold for these, to avoid false impressions due to jitter
        if ($wc_time_taken1 > ($wc_time_taken2 +
                               ($opts{Proportional_Comparison_Time} * $wc_time_taken1)))
        {
            $marker .= "^";
        }
        elsif ($wc_time_taken2 > ($wc_time_taken1 +
                                  ($opts{Proportional_Comparison_Time} * $wc_time_taken2)))
        {
            $marker .= "v";
        }
        else
        {
            $marker .= "-";
        }
    }
    else
    {
            $marker .= "?";
    }

    printf '%1$19s || ' .
        print_result($outcome1, $status1, $loop_count1, $foatp_calls1,
                     $clause_count1, $cpu_time_taken1, $wc_time_taken1) .
        " || " .
        print_result($outcome2, $status2, $loop_count2, $foatp_calls2,
                     $clause_count2, $cpu_time_taken2, $wc_time_taken2) .
        ' || %2$2s' . "\n",
        basename($prob),
        $marker;
}

exit 0;
